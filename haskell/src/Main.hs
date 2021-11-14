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
            stmts ← statements
            sig ← getSig
            return (sig, stmts)
