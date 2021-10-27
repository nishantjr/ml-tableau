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

type Parser x = PState → Either PState (PState, x)

anychar ∷ Parser Char
anychar ps@(PS "") = Left ps
anychar (PS (firstchar:rest) ) = Right (PS rest, firstchar)

char ∷ Char → Parser ()
char _ ps@(PS "") = Left ps
char c ps@(PS (c':rest))
    | c == c'   = Right (PS rest, ())
    | otherwise = Left  ps
