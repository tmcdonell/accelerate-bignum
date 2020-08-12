{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
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
import Test.Types
import Test.ShowType

import qualified Data.Array.Accelerate                              as A

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_eq :: RunN -> TestTree
test_eq runN =
  testGroup "Eq"
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
    testElt :: (Iso a b, Eq a, Eq b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "(==)" $ prop_eq a b
        , testProperty "(/=)" $ prop_neq a b
        ]

    testAcc :: (Show a, Eq a, A.Eq a, Show (ArgType a))
            => Gen a
            -> TestTree
    testAcc a =
      testGroup (showType a)
        [ testProperty "(==)" $ prop_acc_eq runN a
        , testProperty "(/=)" $ prop_acc_neq runN a
        ]


prop_eq
    :: (Iso a b, Eq a, Eq b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_eq a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary' (==) (==) b x y

prop_neq
    :: (Iso a b, Eq a, Eq b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_neq a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary' (/=) (/=) b x y

prop_acc_eq
    :: (Show a, Eq a, A.Eq a)
    => RunN
    -> Gen a
    -> Property
prop_acc_eq runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (==) (A.==) runN x y

prop_acc_neq
    :: (Show a, Eq a, A.Eq a)
    => RunN
    -> Gen a
    -> Property
prop_acc_neq runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (/=) (A./=) runN x y

