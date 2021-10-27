{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} SampleTest

main :: IO ()
main = htfMain htf_importedTests
