{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE UnicodeSyntax #-}
module PatternTest where

import Pattern
import GHC.Base (liftA2)
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

----------------------------------------------------------------------

test_raw_parsers = uncurry assertEqual $ unzip
    $ map (\(input, Parser p, expected) → (expected, p (mkPS input)))
    [ ("foo",    anyChar,    (Right (mkPS "oo", 'f')))
    , ("",       anyChar,    (Left (mkPS "")))
    ]

test_Applicative_TEMP = assertEqual "ab" x
    where
        π            = liftA2 (++) (pure "a") (pure "b")
        (Parser p)   = π
        state        = undefined
        Right (_, x) = p state

test_pure_return = assertEqual (Right 42) (runParser p "")
    where
        p ∷ Parser Int
        p = pure 42

test_run_parsers_of_unit = uncurry assertEqual $ unzip
    $ map (\(input, parser, expected) → (expected, runParser parser input))
    [ ("c",     char 'c',                   Right ())
    , ("cd",    char 'c',                   Left "unconsumed input: \"d...\"")
    , ("d",     char 'c',                   Left "bad parse at \"d...\"")
    , ("",      char 'c',                   Left "bad parse at \"...\"")
    , ("",      nothing,                    Right ())
    , ("cd",    char_cd,                    Right ())
    ]
    where
        nothing, char_cd ∷ Parser ()
        nothing = return ()
        char_cd = do c1 ← char 'c'; c2 ← char 'd'; return c1

test_run_parsers_of_string = uncurry assertEqual $ unzip
    $ map (\(input, parser, expected) → (expected, runParser parser input))
    [ ("abc",   ntimes 3 anyChar,           Right "abc")
    , ("ab",    ntimes 3 anyChar,           Left "bad parse at \"...\"")
    , ("abc",   ntimes 2 anyChar,           Left "unconsumed input: \"c...\"")
    ]
