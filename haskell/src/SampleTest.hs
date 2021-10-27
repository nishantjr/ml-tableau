{-# OPTIONS_GHC -F -pgmF htfpp #-}
module SampleTest where

import Test.Framework

test_failure = assertEqual 0 1
