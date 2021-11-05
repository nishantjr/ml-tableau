{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Pattern

main :: IO ()
main = do
    input ← getContents
    case runParser parser input of
        Left e  → error e
        Right x → print x
    where
        parser = do
            symbols
            string "\n\n  sat "     -- symbols should parse up to this
            gobble
            x ← sig
            return x
