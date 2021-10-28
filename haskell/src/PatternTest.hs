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

test_anychar_success = assertEqual
    (Right (PS "oo", 'f'))          (runParser "foo" anychar)
test_anychar_failure = assertEqual
    (Left (PS ""))                  (runParser "" anychar)
test_char_success = assertEqual
    (Right (PS "d", ()))            (runParser "cd" (char 'c'))
test_char_failure = assertEqual
    (Left  (PS "cd"))               (runParser "cd" (char 'd'))
test_char_failure_empty = assertEqual
    (Left  (PS ""))                 (runParser "" (char 'c'))
