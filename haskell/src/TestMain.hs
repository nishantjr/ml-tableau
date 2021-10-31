{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} PatternTest
import {-@ HTF_TESTS @-} Thing

main :: IO ()
main = htfMain htf_importedTests
