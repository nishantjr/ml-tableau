{-# LANGUAGE UnicodeSyntax #-}

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
    fmap    = undefined
instance Applicative Parser where
    pure    = undefined
    (<*>)   = undefined
instance Monad Parser where
    return  = undefined
    (>>=)   = undefined

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
