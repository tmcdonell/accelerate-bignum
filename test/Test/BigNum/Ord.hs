{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
-- |
-- Module      : Test.BigNum.Ord
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Ord ( test_ord )
  where

import Test.Iso
import Test.Base
import Test.Types
import Test.ShowType

import qualified Data.Array.Accelerate                              as A

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_ord :: RunN -> TestTree
test_ord runN =
  testGroup "Ord"
    [ testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy UU64)
    , testElt i64 (Proxy :: Proxy II64)
    , testAcc w96
    , testAcc i96
    , testAcc w128
    , testAcc i128
    ]
  where
    testElt :: (Iso a b, Ord a, Ord b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "compare" $ prop_compare a b
        ]

    testAcc :: (Ord a, A.Ord a, Show (ArgType a))
            => Gen a
            -> TestTree
    testAcc a =
      testGroup (showType a)
        [ testProperty "(<)"  $ prop_acc_lt runN a
        , testProperty "(>)"  $ prop_acc_gt runN a
        , testProperty "(<=)" $ prop_acc_lte runN a
        , testProperty "(>=)" $ prop_acc_gte runN a
        ]


prop_compare
    :: (Iso a b, Ord a, Ord b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_compare a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary' compare compare b x y

prop_acc_lt
    :: (Ord a, A.Ord a)
    => RunN
    -> Gen a
    -> Property
prop_acc_lt runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (<) (A.<) runN x y

prop_acc_gt
    :: (Ord a, A.Ord a)
    => RunN
    -> Gen a
    -> Property
prop_acc_gt runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (>) (A.>) runN x y

prop_acc_lte
    :: (Ord a, A.Ord a)
    => RunN
    -> Gen a
    -> Property
prop_acc_lte runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (<=) (A.<=) runN x y

prop_acc_gte
    :: (Ord a, A.Ord a)
    => RunN
    -> Gen a
    -> Property
prop_acc_gte runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (>=) (A.>=) runN x y

