{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} PatternTest

main :: IO ()
main = htfMain htf_importedTests
