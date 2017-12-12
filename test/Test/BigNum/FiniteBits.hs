{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
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
import Test.ShowType

import Data.Bits
import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_finitebits :: TestTree
test_finitebits =
  testGroup "FiniteBits"
    [ testElt i64 (Proxy :: Proxy I64)
    , testElt w64 (Proxy :: Proxy U64)
    , testElt i64 (Proxy :: Proxy II64)
    , testElt w64 (Proxy :: Proxy UU64)
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

