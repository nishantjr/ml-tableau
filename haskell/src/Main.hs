{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Pattern

main :: IO ()
main = do
    input ← getContents
    case runParser parser input of
        Left e  → error e
        Right (sig,stmts) → print sig >> print stmts
    where
        parser = do
            stmts ← statements
            sig ← getSig
            return (sig, stmts)
