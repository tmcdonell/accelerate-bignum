{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Test.BigNum.Num
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Num ( test_num )
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


test_num :: RunN -> TestTree
test_num runN =
  testGroup "Num"
    [ testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy II64)
    , testElt w64 (Proxy :: Proxy UU64)
    , testAcc w96
    , testAcc i96
    , testAcc w128
    , testAcc i128
    ]
  where
    testElt :: (Iso a b, Eq a, Eq b, Num a, Num b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "negate"      $ prop_negate a b
        , testProperty "abs"         $ prop_abs a b
        , testProperty "signum"      $ prop_signum a b
        , testProperty "(+)"         $ prop_add a b
        , testProperty "(-)"         $ prop_sub a b
        , testProperty "(*)"         $ prop_mul a b
        , testProperty "fromInteger" $ prop_fromInteger b
        ]

    testAcc :: (Eq a, Num a, A.Num a, Show (ArgType a))
            => Gen a
            -> TestTree
    testAcc a =
      testGroup (showType a)
        [ testProperty "negate"      $ prop_acc_negate runN a
        , testProperty "abs"         $ prop_acc_abs runN a
        , testProperty "signum"      $ prop_acc_signum runN a
        , testProperty "(+)"         $ prop_acc_add runN a
        , testProperty "(-)"         $ prop_acc_sub runN a
        , testProperty "(*)"         $ prop_acc_mul runN a
        , testProperty "fromInteger" $ prop_acc_fromInteger runN a
        ]


prop_negate
    :: (Iso a b, Num a, Num b, Eq a, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_negate a b =
  property $ do
    x <- forAll a
    prop_unary negate negate b x

prop_abs
    :: (Iso a b, Num a, Num b, Eq a, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_abs a b =
  property $ do
    x <- forAll a
    prop_unary abs abs b x

prop_signum
    :: (Iso a b, Num a, Num b, Eq a, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_signum a b =
  property $ do
    x <- forAll a
    prop_unary signum signum b x

prop_add
    :: (Iso a b, Num a, Num b, Eq a, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_add a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary (+) (+) b x y

prop_sub
    :: (Iso a b, Num a, Num b, Eq a, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_sub a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary (-) (-) b x y

prop_mul
    :: (Iso a b, Num a, Num b, Eq a, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_mul a b =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_binary (*) (*) b x y

prop_fromInteger
    :: (Iso a b, Num a, Num b, Eq a, Show a, Show b)
    => Proxy b
    -> Property
prop_fromInteger t =
  property $ do
    x <- forAll integer
    fromInteger x === fromIso t (fromInteger x)


prop_acc_negate
    :: (Num a, A.Num a, Eq a)
    => RunN
    -> Gen a
    -> Property
prop_acc_negate runN a =
  property $ do
    x <- forAll a
    prop_acc_unary negate negate runN x

prop_acc_abs
    :: (Num a, A.Num a, Eq a)
    => RunN
    -> Gen a
    -> Property
prop_acc_abs runN a =
  property $ do
    x <- forAll a
    prop_acc_unary abs abs runN x

prop_acc_signum
    :: (Num a, A.Num a, Eq a)
    => RunN
    -> Gen a
    -> Property
prop_acc_signum runN a =
  property $ do
    x <- forAll a
    prop_acc_unary signum signum runN x

prop_acc_add
    :: (Num a, A.Num a, Eq a)
    => RunN
    -> Gen a
    -> Property
prop_acc_add runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (+) (+) runN x y

prop_acc_sub
    :: (Num a, A.Num a, Eq a)
    => RunN
    -> Gen a
    -> Property
prop_acc_sub runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (-) (-) runN x y

prop_acc_mul
    :: (Num a, A.Num a, Eq a)
    => RunN
    -> Gen a
    -> Property
prop_acc_mul runN a =
  property $ do
    x <- forAll a
    y <- forAll a
    prop_acc_binary (*) (*) runN x y

prop_acc_fromInteger
    :: forall proxy a. (Num a, Eq a, A.Num a)
    => RunN
    -> proxy a
    -> Property
prop_acc_fromInteger runN _ =
  property $ do
    x <- forAll integer
    fromInteger x === isoL (runN (A.unit (fromInteger x :: A.Exp a)))

