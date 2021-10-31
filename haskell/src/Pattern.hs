{-# LANGUAGE UnicodeSyntax, InstanceSigs #-}

module Pattern where

import GHC.Base (liftA2)
import Data.Char (isUpper, isLower)

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
-- state  or a parse success, represented by a `Right` of a pair of the new
-- state and a value of type α called a _production_.
--
newtype Parser α = Parser (PState → Either PState (PState, α))

-- A parser has two parts: the "pure" part consisting of the production
-- itself and the rest consisting of the (somewhat hidden) parser state.
-- `fmap` takes a function operating on this pure portion and applies it to
-- a production to make a new production, handling the state as necessary
-- to do this.
--
instance Functor Parser where
    --   (α → β) → f α        → f β
    fmap f         (Parser p) = Parser (\st →
        case (p st) of
             Left st'        → Left st'
             Right (st', x)  → Right (st', f x)
             )
    -- f <$> x = fmap f x       fmap has an infix alias

-- Applicative gives us sequencing of Parsers: `liftA2` runs Parser β after
-- Parser α, threading the the state between them and using the `(α → β → γ)`
-- to combine the productions of the two parsers.
--
-- Applicative also gives us `pure x`, allowing us to create a parser that
-- produces the pure value _x_.
--
instance Applicative Parser where
    pure ∷ α → Parser α
    pure   x = Parser (\st → Right (st, x))

    liftA2 ∷  (α → β → γ) → Parser α  → Parser β → Parser γ
    liftA2    combine      (Parser p₀)  π₁       = Parser (\st →
            case p₀ st of
                Left st'      → Left st'        -- failure passes through
                Right (st',x) → p₁ st' where Parser p₁ = fmap (combine x) π₁
        )

    -- (<*>) ∷ Parser (β → γ) → Parser β → Parser γ
    -- (<*>) = liftA2 id            -- here (β → γ) = α in liftA2 above
                                    -- and we use id ∷ (β → γ) → (β → γ)

-- Monad gives us choice based on intermediate productions in sequenced Parsers.
--
instance Monad Parser where
    -- (return ∷ α → m α) = pure    -- Default definition

    (>>=) ∷ Parser τ   →  (τ → Parser γ) → Parser γ
    (>>=)  (Parser p₀)       f           = Parser (\st →
        case p₀ st of
             Left st'       → Left st'          -- failure passes through
             Right (st', x) → p₁ st' where (Parser p₁) = f x
        )

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
