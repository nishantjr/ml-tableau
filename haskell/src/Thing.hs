{-
    Simple demonstration of defining a Functor etc.
    Also used to demonstrate the "import liftA2" problem we're having.
-}
{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE UnicodeSyntax, InstanceSigs #-}

module Thing where

import Test.Framework

-- XXX If liftA2 is not explicitly imported from GHC.Base, we get:
--      ‘liftA2’ is not a (visible) method of class ‘Applicative’
--
import GHC.Base (liftA2)

----------------------------------------------------------------------

newtype Thing α = Thing α
    deriving (Show, Eq)

instance Functor Thing where
    fmap ∷ (α → β) → Thing α  → Thing β
    fmap   f        (Thing x) = Thing (f x)

instance Applicative Thing where
    pure ∷ α → Thing α
    pure   x = Thing x

    liftA2 ∷ (α → β → γ) → Thing α → Thing β → Thing γ
    liftA2 = undefined

----------------------------------------------------------------------

test_fmap = assertEqual (Thing 3) $ fmap (+1) (Thing 2)
test_pure = assertEqual (Thing 4) (pure 4)
