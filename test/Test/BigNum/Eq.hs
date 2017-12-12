{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Module      : Test.BigNum.Eq
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Eq ( test_eq )
  where

import Test.Iso
import Test.Base
import Test.ShowType

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_eq :: TestTree
test_eq =
  testGroup "Eq"
    [ testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy II64)
    , testElt w64 (Proxy :: Proxy UU64)
    ]
  where
    testElt :: (Iso a b, Eq a, Eq b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt e p =
      testGroup (showType p)
        [ testProperty "(==)" $ prop_eq e p
        , testProperty "(/=)" $ prop_neq e p
        ]


prop_eq
    :: (Iso a b, Eq a, Eq b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_eq a p =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary' (==) (==) p x y

prop_neq
    :: (Iso a b, Eq a, Eq b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_neq a p =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary' (/=) (/=) p x y

