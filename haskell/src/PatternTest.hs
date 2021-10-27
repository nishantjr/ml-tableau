{-# OPTIONS_GHC -F -pgmF htfpp #-}
module PatternTest where

import Pattern
import Test.Framework

test_Pat_syntax_example = assertEqual xs xs
    where
        xs = [ x, s
             , x :∧ s, x :∨ s
             , f [s, x], df []
             , Top, Bot
             , Exists "x" $ f [x :∧ s]
             , Forall "x" $ f [x :∧ s]
             , Mu "X" $ z :∨ f [s]
             , Nu "X" $ z :∧ f [s]

             ]
        x  = EVar "x"
        s  = SVar "X"
        z  = App "z" []
        f  = App  "f"
        df = DApp "f"
