{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
-- |
-- Module      : Test.BigNum.FiniteBits
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.FiniteBits ( test_finitebits )
  where

import Test.Iso
import Test.Base
import Test.Types
import Test.ShowType

import qualified Data.Array.Accelerate.Data.Bits                    as A

import Data.Bits
import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_finitebits :: RunN -> TestTree
test_finitebits runN =
  testGroup "FiniteBits"
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
    testElt :: (Iso a b, Eq a, Eq b, FiniteBits a, FiniteBits b, Show a, Show b, Show (ArgType b))
            => Gen a
            -> Proxy b
            -> TestTree
    testElt a b =
      testGroup (showType b)
        [ testProperty "countLeadingZeros"  $ prop_clz a b
        , testProperty "countTrailingZeros" $ prop_ctz a b
        ]

    testAcc :: (Eq a, FiniteBits a, A.FiniteBits a, Show (ArgType a))
            => Gen a
            -> TestTree
    testAcc a =
      testGroup (showType a)
        [ testProperty "countLeadingZeros"  $ prop_acc_clz runN a
        , testProperty "countTrailingZeros" $ prop_acc_ctz runN a
        ]


prop_clz
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_clz a b =
  property $ do
    x <- forAll a
    prop_unary' countLeadingZeros countLeadingZeros b x

prop_ctz
    :: (Iso a b, FiniteBits a, FiniteBits b, Show a, Show b)
    => Gen a
    -> Proxy b
    -> Property
prop_ctz a b =
  property $ do
    x <- forAll a
    prop_unary' countTrailingZeros countTrailingZeros b x

prop_acc_clz
    :: (FiniteBits a, A.FiniteBits a)
    => RunN
    -> Gen a
    -> Property
prop_acc_clz runN a =
  property $ do
    x <- forAll a
    prop_acc_unary countLeadingZeros  A.countLeadingZeros runN x

prop_acc_ctz
    :: (FiniteBits a, A.FiniteBits a)
    => RunN
    -> Gen a
    -> Property
prop_acc_ctz runN a =
  property $ do
    x <- forAll a
    prop_acc_unary countTrailingZeros A.countTrailingZeros runN x

