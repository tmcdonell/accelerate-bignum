{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Module      : Test.BigNum.Enum
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Enum ( test_enum )
  where

import Test.Iso
import Test.Base
import Test.Types
import Test.ShowType

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_enum :: TestTree
test_enum =
  testGroup "Enum"
    [ testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy II64)
    , testElt w64 (Proxy :: Proxy UU64)
    ]
  where
    testElt :: (Iso a b, Eq a, Bounded a, Enum a, Enum b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "succ" $ prop_succ a b
        , testProperty "pred" $ prop_pred a b
        ]


prop_succ
    :: (Iso a b, Bounded a, Enum a, Enum b, Eq a, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_succ a b =
  property $ do
    x <- forAll (a `except` (== maxBound))
    succ x === with_unary b succ x

prop_pred
    :: (Iso a b, Bounded a, Enum a, Enum b, Eq a, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_pred a b =
  property $ do
    x <- forAll (a `except` (== minBound))
    pred x === with_unary b pred x

