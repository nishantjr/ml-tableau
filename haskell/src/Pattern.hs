{-# LANGUAGE UnicodeSyntax, InstanceSigs #-}

module Pattern where

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

data PState = PS
    { input ∷ String
    }
    deriving (Show, Eq)

newtype Parser x = Parser (PState → Either PState (PState, x))

instance Functor Parser where
    --   (a → b) → f a        → f b
    fmap f         (Parser p) = Parser (\st →
        case (p st) of
             Left st'        → Left st'
             Right (st', x)  → Right (st', f x)
             )
instance Applicative Parser where
    --   a → f a
    pure x = Parser (\st → Right (st, x))
    (<*>) ∷ Parser (a → b) → Parser a → Parser b
    (Parser p₀)  <*> π = Parser (\st →
        case p₀ st of
             Left st'        → Left st'
             Right (st', f)  → let Parser p = (fmap f π) in p st'
        )
instance Monad Parser where
    -- (return :: a → m a) = pure
    --    m a   →  (a → m b) → m b
    (Parser p) >>= f         = Parser (\st →
        case p st of
             Left st'       → Left st'
             Right (st', x) → let Parser p = (f x) in p st'
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
