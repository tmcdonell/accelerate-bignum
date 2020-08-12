{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Test.BigNum.Bounded
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum.Bounded ( test_bounded )
  where

import Test.Iso
import Test.Base
import Test.Types
import Test.ShowType

import Data.Array.Accelerate.Data.BigInt
import Data.Array.Accelerate.Data.BigWord
import qualified Data.Array.Accelerate                              as A

import Data.Proxy
import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog


test_bounded :: RunN -> TestTree
test_bounded runN =
  testGroup "Bounded"
    [ testElt (Proxy :: Proxy U64)
    , testElt (Proxy :: Proxy I64)
    , testElt (Proxy :: Proxy UU64)
    , testElt (Proxy :: Proxy II64)
    , testAcc (Proxy :: Proxy Word96)
    , testAcc (Proxy :: Proxy Int96)
    , testAcc (Proxy :: Proxy Word128)
    , testAcc (Proxy :: Proxy Int128)
    ]
  where
    testElt :: (Iso a b, Eq a, Bounded a, Bounded b, Show a, Show b, Show (ArgType b))
            => Proxy b
            -> TestTree
    testElt p =
      testGroup (showType p)
        [ testProperty "minBound" $ prop_minBound p
        , testProperty "maxBound" $ prop_maxBound p
        ]

    testAcc :: (Show a, Eq a, Bounded a, A.Bounded a, Show (ArgType a))
            => Proxy a
            -> TestTree
    testAcc p =
      testGroup (showType p)
        [ testProperty "minBound" $ prop_acc_minBound runN p
        , testProperty "maxBound" $ prop_acc_maxBound runN p
        ]


prop_minBound
    :: (Iso a b, Bounded a, Bounded b, Eq a, Show a)
    => Proxy b
    -> Property
prop_minBound p =
  property $
    minBound === fromIso p minBound

prop_maxBound
    :: (Iso a b, Bounded a, Bounded b, Eq a, Show a)
    => Proxy b
    -> Property
prop_maxBound p =
  property $
    maxBound === fromIso p maxBound

prop_acc_minBound
    :: forall a. (Show a, Eq a, Bounded a, A.Bounded a)
    => RunN
    -> Proxy a
    -> Property
prop_acc_minBound runN _ =
  property $
    minBound === isoL (runN (A.unit (minBound :: A.Exp a)))

prop_acc_maxBound
    :: forall a. (Show a, Eq a, Bounded a, A.Bounded a)
    => RunN
    -> Proxy a
    -> Property
prop_acc_maxBound runN _ =
  property $
    maxBound === isoL (runN (A.unit (maxBound :: A.Exp a)))

