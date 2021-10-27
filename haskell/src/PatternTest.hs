{-# OPTIONS_GHC -F -pgmF htfpp #-}
module PatternTest where

import Pattern
import Test.Framework

test_Pat_singleton
    = assertEqual [EVar "x", SVar "X"] [EVar "x", SVar "X"]

test_and
    = assertEqual (x :∧ x) (x :∧ x)
    where x = EVar "x"
