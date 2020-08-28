{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
-- |
-- Module      : Test.Types
-- Copyright   : [2017..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Test.Types where

import Test.Iso

import Data.Array.Accelerate.Data.BigInt
import Data.Array.Accelerate.Data.BigWord

import Data.Bits
import Data.Int
import Data.Word


newtype I64 = I64 (BigInt  Int32  Word32)
  deriving (Show, Eq, Ord, Bounded, Num, Real, Enum, Integral, Bits, FiniteBits)

newtype U64 = U64 (BigWord Word32 Word32)
  deriving (Show, Eq, Ord, Bounded, Num, Real, Enum, Integral, Bits, FiniteBits)

newtype II64 = II64 (BigInt  Int16  (BigWord Word16 Word32))
  deriving (Show, Eq, Ord, Bounded, Num, Real, Enum, Integral, Bits, FiniteBits)

newtype UU64 = UU64 (BigWord Word16 (BigWord Word16 Word32))
  deriving (Show, Eq, Ord, Bounded, Num, Real, Enum, Integral, Bits, FiniteBits)

instance Iso Int64 I64 where
  isoR w              = I64 (I2 (fromIntegral (w `shiftR` 32)) (fromIntegral w))
  isoL (I64 (I2 h l)) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Word64 U64 where
  isoR w              = U64 (W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w))
  isoL (U64 (W2 h l)) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Int64 II64 where
  isoR w
    = II64 (I2 (fromIntegral (w `shiftR` 48)) (W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w)))

  isoL (II64 (I2 h (W2 lh ll)))
    =  fromIntegral h  `shiftL` 48
   .|. fromIntegral lh `shiftL` 32
   .|. fromIntegral ll

instance Iso Word64 UU64 where
  isoR w
    = UU64 (W2 (fromIntegral (w `shiftR` 48)) (W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w)))

  isoL (UU64 (W2 h (W2 lh ll)))
    =  fromIntegral h  `shiftL` 48
   .|. fromIntegral lh `shiftL` 32
   .|. fromIntegral ll

