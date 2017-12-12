{-# LANGUAGE RankNTypes #-}
-- |
-- Module      : Test.BigNum
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.BigNum where

import Test.Base
import Test.BigNum.Num2
import Test.BigNum.Eq
import Test.BigNum.Ord
import Test.BigNum.Bounded
import Test.BigNum.Enum
import Test.BigNum.Num
import Test.BigNum.Real
import Test.BigNum.Integral
import Test.BigNum.Bits
import Test.BigNum.FiniteBits

import Test.Tasty
import System.Environment


bignum :: RunN -> IO ()
bignum runN = do
  setEnv "TASTY_HEDGEHOG_TESTS" "1000"
  me <- getProgName
  defaultMain $
    testGroup me
      [ test_num2
      , test_eq
      , test_ord
      , test_bounded
      , test_enum
      , test_num
      , test_real
      , test_integral
      , test_bits
      , test_finitebits
      ]

