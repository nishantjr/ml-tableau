{-# LANGUAGE UnicodeSyntax, InstanceSigs #-}

module Pattern where

import GHC.Base (liftA2)
import Data.Char (isUpper, isLower)
import Data.Map.Strict (Map, fromList)

----------------------------------------------------------------------
-- A Signature is a mapping from symbol name to arity

newtype Signature = Signature (Map String Int)
    deriving (Show, Eq)

sample_symbols ∷ Signature
sample_symbols = Signature (fromList [("C",0),("S",1)])

----------------------------------------------------------------------

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
    { input ∷ String
    }
    deriving (Show, Eq)

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
runParser (Parser p) input =
    case p (PS input) of
        Left state                          → Left "bad parse"
        Right (PS input, x) | input == ""   → Right x
                            | otherwise     → Left "unconsumed input"

anychar ∷ Parser Char
anychar = Parser (\st@(PS inp) → case inp of
    (c:cs)  → Right (PS cs, c)
    _       → Left st
    )

char ∷ Char → Parser ()
char c' = Parser (\st@(PS inp) → case inp of
    (c:cs) | c == c'    → Right (PS cs, ())
    _                   → Left st
    )
