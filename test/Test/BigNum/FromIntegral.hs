{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Test.BigNum.FromIntegral
-- Copyright   : [2017..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.FromIntegral ( test_fromIntegral )
  where

import Test.Iso
import Test.Base
import Test.ShowType

import Data.Array.Accelerate.Data.BigInt
import Data.Array.Accelerate.Data.BigWord

import Data.Array.Accelerate                                        ( Exp )
import qualified Data.Array.Accelerate                              as A

import Data.Int
import Data.Proxy
import Data.Word
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog
import Text.Printf


test_fromIntegral :: RunN -> TestTree
test_fromIntegral runN =
  testGroup "FromIntegral"
    [ -- little -> big
      testElt w32 (Proxy::Proxy Word128)
    , testElt w32 (Proxy::Proxy Word192)
    , testElt w32 (Proxy::Proxy Int128)
    , testElt w32 (Proxy::Proxy Int192)
    , testElt i32 (Proxy::Proxy Word128)
    , testElt i32 (Proxy::Proxy Word192)
    , testElt i32 (Proxy::Proxy Int128)
    , testElt i32 (Proxy::Proxy Int192)
    , testElt w64 (Proxy::Proxy Word128)
    , testElt w64 (Proxy::Proxy Word192)
    , testElt w64 (Proxy::Proxy Int128)
    , testElt w64 (Proxy::Proxy Int192)
    , testElt i64 (Proxy::Proxy Word128)
    , testElt i64 (Proxy::Proxy Word192)
    , testElt i64 (Proxy::Proxy Int128)
    , testElt i64 (Proxy::Proxy Int192)
    -- big -> little
    , testElt w128 (Proxy::Proxy Word32)
    , testElt w192 (Proxy::Proxy Word32)
    , testElt i128 (Proxy::Proxy Word32)
    , testElt i192 (Proxy::Proxy Word32)
    , testElt w128 (Proxy::Proxy Word64)
    , testElt w192 (Proxy::Proxy Word64)
    , testElt i128 (Proxy::Proxy Word64)
    , testElt i192 (Proxy::Proxy Word64)
    , testElt w128 (Proxy::Proxy Int32)
    , testElt w192 (Proxy::Proxy Int32)
    , testElt i128 (Proxy::Proxy Int32)
    , testElt i192 (Proxy::Proxy Int32)
    , testElt w128 (Proxy::Proxy Int64)
    , testElt w192 (Proxy::Proxy Int64)
    , testElt i128 (Proxy::Proxy Int64)
    , testElt i192 (Proxy::Proxy Int64)
    ]
  where
    testElt
        :: (Show a, Show b, Integral a, Num b, Eq b, A.Integral a, A.Num b, A.FromIntegral a b, Show (ArgType a), Show (ArgType b))
        => Gen a
        -> Proxy b
        -> TestTree
    testElt a b =
      testProperty (printf "%s->%s" (showType a) (showType b)) $ prop_fromIntegral runN a b


prop_fromIntegral
    :: forall a b. (Show a, Show b, Integral a, Num b, Eq b, A.Integral a, A.Num b, A.FromIntegral a b)
    => RunN
    -> Gen a
    -> Proxy b
    -> Property
prop_fromIntegral runN a _ =
  property $ do
    x <- forAll a
    prop_acc_unary fromIntegral (A.fromIntegral :: Exp a -> Exp b) runN x

