-- |
-- Module      : Data.Array.Accelerate.Data.BigInt
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Fixed length signed integer types
--

module Data.Array.Accelerate.Data.BigInt (

  Int96,
  Int128,
  Int160,
  Int192,
  Int224,
  Int256,
  Int512,

  -- ** Internals
  BigInt(..)

) where

import Data.Int
import Data.Word
import Data.Array.Accelerate.Data.BigWord
import Data.Array.Accelerate.Data.Internal.BigInt

type Int96  = BigInt  Int32  Word64
type Int128 = BigInt  Int64  Word64
type Int160 = BigInt  Int32 Word128
type Int192 = BigInt  Int64 Word128
type Int224 = BigInt  Int32 Word192
type Int256 = BigInt Int128 Word128
type Int512 = BigInt Int256 Word256

