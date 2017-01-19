-- |
-- Module      : Data.Array.Accelerate.Data.BigWord
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Fixed length unsigned word types

module Data.Array.Accelerate.Data.BigWord (

  Word96,
  Word128,
  Word160,
  Word192,
  Word224,
  Word256,
  Word512,

  -- ** Internals
  BigWord(..)

) where

import Data.Word
import Data.Array.Accelerate.Data.Internal.BigWord

type Word96  = BigWord  Word32  Word64
type Word128 = BigWord  Word64  Word64
type Word160 = BigWord  Word32 Word128
type Word192 = BigWord  Word64 Word128
type Word224 = BigWord  Word32 Word192
type Word256 = BigWord Word128 Word128
type Word512 = BigWord Word256 Word256

