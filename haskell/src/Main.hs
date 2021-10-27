module Main where

import SampleTest (htf_SampleTest_thisModulesTests)
import Test.Framework (htfMain)

main :: IO ()
main = htfMain htf_SampleTest_thisModulesTests
