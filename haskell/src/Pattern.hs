{-# LANGUAGE UnicodeSyntax, InstanceSigs #-}

module Pattern where

import Control.Applicative
import Data.Char (isUpper, isLower, isSpace)
import qualified Data.Map.Strict as M (Map, fromList, empty, insert)

----------------------------------------------------------------------
-- A Signature is a mapping from symbol name to arity

type Signature = M.Map String Int

sample_symbols ∷ Signature
sample_symbols = M.fromList [("C",0),("S",1)]

----------------------------------------------------------------------

data Statement = Sat Pat | Unsat Pat | Valid Pat
    deriving (Show, Eq)

data Pat
    = EVar   String
    | SVar   String
    | Top                   | Bot
    | Pat :∧ Pat            | Pat :∨ Pat
    | App    String [Pat]   | DApp   String [Pat]
    | Exists String  Pat    | Forall String  Pat
    | Mu     String  Pat    | Nu     String  Pat
    deriving (Show, Eq)

parsePat ∷ String → Pat
parsePat "⊥"                 = Bot
parsePat "⊤"                 = Top
parsePat (x:xs) | isLower(x) = EVar (x:xs)
parsePat (x:xs) | isUpper(x) = SVar (x:xs)
parsePat _ = error "Bad input"

----------------------------------------------------------------------
-- Parser

-- A parser state includes the current input to be parsed, error
-- information, and anything else necessary to making the parser work
-- nicely.
data PState = PS
    { signature ∷ Signature
    , input     ∷ String
    }
    deriving (Show, Eq)

mkPS :: String → PState
mkPS s = PS M.empty s

-- A _parser of α_ is a function that, when applied to a parser _state_
-- evaluates to a parse failure, represented by a `Left` of the failure
-- state or a parse success, represented by a `Right` of a pair of the new
-- state and a value of type α called a _production_.
--
newtype Parser α = Parser (PState → Either PState (PState, α))

-- Parsers may be combined, letting us build complex parsers from a library
-- of smaller parsers called combinators. To do this, we make Parser α an
-- instance of Monad, which gives us:
-- * Encapsulation of state so that higher-level combinators can handle
--   it implicitly. (Functor)
-- * Sequencing of parsers, with the state threaded through them.
--   (Applicative)
-- * Error handling, via failure also being threaded through sequences
--   by not trying to execute subsequent parsers after a failure. (Applicative)
-- * Choice (of what to do next) based on intermediate productions in
--   a sequence of parsers. (Monad)
-- Further explanation of this is given in the instance definitions for
-- Applicative and Functor below.
--
-- The Monad typeclass supplies choice with the (τ → Parser γ) argument
-- to bind (>>=), allowing us to choose the next parser based on the
-- production produced by the previous parser.
--
instance Monad Parser where
    return ∷ α → Parser α
    return   x = Parser (\st → Right (st, x))

    (>>=) ∷ Parser τ   →  (τ → Parser γ) → Parser γ
    (>>=)  (Parser p₀)       f           = Parser (\st →
        case p₀ st of
             Left st'       → Left st'          -- failure passes through
             Right (st', x) → p₁ st' where (Parser p₁) = f x
        )

-- PEG parsers work by working through a list of alternatives and picking the
-- first one that succeeds. The `Alternative` class gives us this with the `<|>`
-- operator (creating a parser for the union of the languages of the two
-- parsers), and also gives us two operations that are built on this:
-- * `many`: try the given parser repeatedly until it fails, collecting the
--   results in a list.
-- * `some`: as with `many`, but fail unless the parser is successful at least
--   once.
--
-- `empty` is the identity element for the choice function; if given as one
-- argument the choice always selects the other. It is the parser for the empty
-- language. In our current implementation simple failure works because failure
-- does not change the state. However, if failure does start changing the state
-- at some point we will need to change this to ensure that the other choice's
-- failure is always chosen over empty's.
--
instance Alternative Parser where
    empty ∷ Parser a
    empty = Parser $ \st → Left st

    (<|>) ∷ Parser α → Parser α → Parser α
    (Parser p) <|> (Parser q)  = Parser $ \st →
        case p st of
            Left _      → q st
            right       → right

-- Applicative gives us sequencing of Parsers: `liftA2` runs Parser β after
-- Parser α, threading the the state between them and using the `(α → β →
-- γ)` to combine the productions of the two parsers, and also `pure x`,
-- allowing us to create a parser that produces the pure value _x_. (See
-- Functor below for more on pure values.)
--
-- This can be entirely defined using Monad operations since all Monads are
-- Applicative functors. However, the language design doesn't give a way to
-- have these automatically defined in this way only if this particular
-- Applicative is also an instance of Monad, so we need to do this by hand.
--
instance Applicative Parser where
    pure ∷ α → Parser α
    pure     = return

    liftA2 ∷  (α → β → γ) → Parser α  → Parser β → Parser γ
    liftA2 f π ρ = do x ← π; y ← ρ; return (f x y)

    -- (<*>) ∷ Parser (β → γ) → Parser β → Parser γ
    -- (<*>) = liftA2 id            -- here (β → γ) = α in liftA2 above
                                    -- and we use id ∷ (β → γ) → (β → γ)
    -- π <*> ρ = do f ← π; y ← ρ; return (f y)


-- A parser has two parts: the "pure" part consisting of the production
-- itself and the rest consisting of the (somewhat hidden) parser state.
-- `fmap` takes a function operating on this pure portion and applies it to
-- a production to make a new production, handling the state as necessary
-- to do this.
--
instance Functor Parser where
    --   (α → β) → f α → f β
    fmap f         π   = do x ← π; return (f x)
    -- `fmap` also has an infix alias:
    -- f <$> x = fmap f x

runParser ∷ Parser a → String → Either String a
runParser (Parser p) s =
    case p (mkPS s) of
        Left st                         → err st "bad parse at"
        Right (st, x) | input st == ""  → Right x
                      | otherwise       → err st "unconsumed input:"
    where
        err st msg = Left $ msg ++ " " ++ (show $ take 12 (input st) ++ "...")

----------------------------------------------------------------------
-- Low-level Combinators

getState :: Parser PState
getState = Parser $ \st → Right (st,st)

setState ∷ (PState → PState) → Parser ()
setState f = Parser $ \st → Right (f st, ())

-- Consume all remaining input
gobble :: Parser ()
gobble = Parser $ \st → Right (st { input="" }, ())

anyChar ∷ Parser Char
anyChar = Parser (\st → case (input st) of
    (c:cs)  → Right (st { input=cs }, c)
    _       → Left st
    )

char ∷ Char → Parser ()
char c' = Parser (\st → case (input st) of
    (c:cs) | c == c'    → Right (st { input=cs }, ())
    _                   → Left st
    )

----------------------------------------------------------------------
-- Generic Combinators

string ∷ String → Parser ()
string = mapM_ char

-- Optional whitespace
optspaces :: Parser ()
optspaces = many space >> return ()

-- Mandatory whitespace
toksep :: Parser ()
toksep = some space >> return ()

space = matches anyChar isSpace >> return ()

nat :: Parser Int
nat = do digits ← many digit
         return $ read digits

digit ∷ Parser Char
digit = anyChar `matches` isDigit
    where isDigit c = (c >= '0') && (c <= '9')

matches :: Parser α → (α → Bool) → Parser α
matches π f = do x ← π
                 if f x then return x
                        else empty

----------------------------------------------------------------------
-- Pattern Combinators

statements :: Parser [Statement]
statements = do
    many $ optspaces >> (symbols <|> statement)
    optspaces
    return []

getSig ∷ Parser Signature
getSig = getState >>= return . signature

symbols :: Parser ()
symbols = do
    string "symbols"
    many $ toksep >> symbolDeclaration
    char ';'

symbolDeclaration :: Parser ()
symbolDeclaration = do
    namechar ← anyChar
    let name = [namechar]
    char ':'
    arity ← nat
    addSymbol name arity

addSymbol :: String → Int → Parser ()
addSymbol name arity = setState $ \st →
    st { signature = M.insert name arity (signature st) }

statement :: Parser ()
statement = do
    stmt <- sat <|> unsat <|> valid
    --return stmt
    return ()

sat, unsat, valid :: Parser Statement
sat   = parameterizedStatement "sat"   Sat
unsat = parameterizedStatement "unsat" Unsat
valid = parameterizedStatement "valid" Valid

parameterizedStatement :: String → (Pat → Statement) → Parser Statement
parameterizedStatement s cons = do
    string s
    toksep
    pat ← pattern
    optspaces
    char ';'
    return $ cons pat

pattern :: Parser Pat
pattern = do
    some $ matches anyChar (';' /=)
    return $ EVar "XXX"
