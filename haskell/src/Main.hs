{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Pattern
import Data.Composition
import Data.Key (mapWithKeyM_)

main :: IO ()
main = do
    input ← getContents
    case runParser parser input of
        Left e  → error e
        Right x → printout x
    where
        parser = do
            stmts ← statements
            sig ← getSig
            return (sig, stmts)
        printout ∷ (Signature, [Statement]) → IO ()
        printout (sig, stmts) = do
            mapWithKeyM_ (print .: (,)) sig
            mapM_ print stmts
