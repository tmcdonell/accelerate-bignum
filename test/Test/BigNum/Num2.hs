{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeFamilies     #-}
-- |
-- Module      : Test.BigNum.Num2
-- Copyright   : [2017..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Num2 ( test_num2 )
  where

import Test.Base
import Test.Iso
import Test.ShowType

import Data.Array.Accelerate.Data.BigInt
import Data.Array.Accelerate                                        ( Elt, Exp, Plain, Lift )
import qualified Data.Array.Accelerate                              as A

import Data.Bits
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_num2 :: RunN -> TestTree
test_num2 runN =
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
    testElt :: ( Show e, Num2 e, Integral e, Show e, Show (ArgType e), FiniteBits (Unsigned e), Integral (Unsigned e)
               , Num2 (Exp e), Elt e, Elt (Unsigned e), Lift Exp (Unsigned (Exp e)), Plain (Unsigned (Exp e)) ~ Unsigned e )
            => Gen e
            -> TestTree
    testElt e =
      testGroup (showType e)
        [ testProperty "addWithCarry" $ prop_addWithCarry e
        , testProperty "mulWithCarry" $ prop_mulWithCarry e
        --
        , testProperty "addWithCarry" $ prop_acc_addWithCarry runN e
        , testProperty "mulWithCarry" $ prop_acc_mulWithCarry runN e
        ]


prop_addWithCarry
    :: (Show e, Num2 e, Integral e, Show e, FiniteBits (Unsigned e), Integral (Unsigned e))
    => Gen e
    -> Property
prop_addWithCarry e =
  property $ do
    x <- forAll e
    y <- forAll e
    uncurry toInteger2 (addWithCarry x y) === toInteger x + toInteger y

prop_mulWithCarry
    :: (Show e, Num2 e, Integral e, Show e, FiniteBits (Unsigned e), Integral (Unsigned e))
    => Gen e
    -> Property
prop_mulWithCarry e =
  property $ do
    x <- forAll e
    y <- forAll e
    uncurry toInteger2 (mulWithCarry x y) === toInteger x * toInteger y

prop_acc_addWithCarry
    :: ( Show e, Num2 (Exp e), Integral e, FiniteBits (Unsigned e), Integral (Unsigned e)
       , Elt e, Elt (Unsigned e), Lift Exp (Unsigned (Exp e)), Plain (Unsigned (Exp e)) ~ Unsigned e )
    => RunN
    -> Gen e
    -> Property
prop_acc_addWithCarry runN e =
  property $ do
    x <- forAll e
    y <- forAll e
    uncurry toInteger2 (with_acc_binary runN (A.lift $$ addWithCarry) x y) === toInteger x + toInteger y

prop_acc_mulWithCarry
    :: ( Show e, Num2 (Exp e), Integral e, FiniteBits (Unsigned e), Integral (Unsigned e)
       , Elt e, Elt (Unsigned e), Lift Exp (Unsigned (Exp e)), Plain (Unsigned (Exp e)) ~ Unsigned e )
    => RunN
    -> Gen e
    -> Property
prop_acc_mulWithCarry runN e =
  property $ do
    x <- forAll e
    y <- forAll e
    uncurry toInteger2 (with_acc_binary runN (A.lift $$ mulWithCarry) x y) === toInteger x * toInteger y

