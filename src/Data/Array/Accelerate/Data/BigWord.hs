-- |
-- Module      : Data.Array.Accelerate.Data.BigWord
-- Copyright   : [2016..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
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
  BigWord(..),
  Num2(..),

) where

import Data.Array.Accelerate.Internal.Num2
import Data.Array.Accelerate.Internal.BigWord
import Data.Array.Accelerate.Internal.Orphans ()

