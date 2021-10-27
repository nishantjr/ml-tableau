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

-- map     :: (a -> b) -> [a] -> [b]
-- unzip   :: [(a, b)] -> ([a], [b])
-- uncurry :: (a -> b -> c) -> (a, b) -> c
xxx_test_Pat_parse = uncurry assertEqual $ unzip
        $ map (\(input, expected) -> (expected, parsePat input))
        [ ("⊥",         Bot)
        , ("⊤",         Top)
        , ("x",         EVar "x")
        , ("X",         SVar "X")
        , ("x ",        EVar "x")
        ]

test_anychar_success = assertEqual (anychar (PS "foo")) (Right (PS "oo", 'f'))
test_anychar_failure = assertEqual (anychar (PS "")) (Left (PS ""))

test_char_success   = assertEqual (char 'c' (PS "cd")) (Right (PS "d", ()))
test_char_failure   = assertEqual (char 'd' (PS "cd")) (Left  (PS "cd"))
