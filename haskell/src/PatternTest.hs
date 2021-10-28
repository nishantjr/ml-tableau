{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE UnicodeSyntax #-}
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

test_raw_parsers = uncurry assertEqual $ unzip
    $ map (\(input, Parser p, expected) → (expected, p (PS input)))
    [ ("foo",    anychar,    (Right (PS "oo", 'f')))
    , ("",       anychar,    (Left (PS "")))
    ]

test_run_parsers = uncurry assertEqual $ unzip
    $ map (\(input, parser, expected) → (expected, runParser parser input))
    [ ("c",     char 'c',                   Right ())
    , ("cd",    char 'c',                   Left "unconsumed input")
    , ("d",     char 'c',                   Left "bad parse")
    , ("",      char 'c',                   Left "bad parse")
    ]
