{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Pattern
import Data.Map (mapWithKey)
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
            print sig
            -- XXX Trying to print the signature in nicer form....
            -- (XXX Remember to remove unneeded imports after this is working.)
            -- mapWithKeyM_ (print . (,)) sig
            mapM_ print stmts
