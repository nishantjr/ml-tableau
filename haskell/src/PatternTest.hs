{-# OPTIONS_GHC -F -pgmF htfpp #-}
module PatternTest where

import Pattern
import Test.Framework

test_Pat_syntax_example = assertEqual xs xs
    where
        xs = [ ex, sx, ex :∧ sx, ex :∨ sx, f [sx, ex] ]
        ex = EVar "x"
        sx = SVar "X"
        f  = App "f"
