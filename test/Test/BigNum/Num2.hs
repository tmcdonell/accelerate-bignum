{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Module      : Test.BigNum.Num2
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Num2 ( test_num2 )
  where

import Test.Base
import Test.ShowType

import Data.Array.Accelerate.Data.BigInt

import Data.Bits
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_num2 :: TestTree
test_num2 =
  testGroup "Num2"
    [ testElt w8
    , testElt w16
    , testElt w32
    , testElt w64
    , testElt i8
    , testElt i16
    , testElt i32
    , testElt i64
    ]
  where
    testElt :: (Num2 e, Integral e, Show e, Show (ArgType e), FiniteBits (Unsigned e), Integral (Unsigned e))
            => Gen e
            -> TestTree
    testElt e =
      testGroup (showType e)
        [ testProperty "addWithCarry" $ prop_addWithCarry e
        , testProperty "mulWithCarry" $ prop_mulWithCarry e
        ]


prop_addWithCarry
    :: (Num2 e, Integral e, Show e, FiniteBits (Unsigned e), Integral (Unsigned e))
    => Gen e
    -> Property
prop_addWithCarry e =
  property $ do
    x <- forAll e
    y <- forAll e
    uncurry toInteger2 (addWithCarry x y) === toInteger x + toInteger y

prop_mulWithCarry
    :: (Num2 e, Integral e, Show e, FiniteBits (Unsigned e), Integral (Unsigned e))
    => Gen e
    -> Property
prop_mulWithCarry e =
  property $ do
    x <- forAll e
    y <- forAll e
    uncurry toInteger2 (mulWithCarry x y) === toInteger x * toInteger y

