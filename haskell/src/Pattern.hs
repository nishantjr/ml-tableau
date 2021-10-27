{-# LANGUAGE UnicodeSyntax #-}

module Pattern where

data Pat
    = EVar String | SVar String
    | Pat :∧ Pat | Pat :∨ Pat
    -- | App String [Pat]
    deriving (Show, Eq)
