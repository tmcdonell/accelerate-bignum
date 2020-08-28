{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Internal.Orphans.Elt
-- Copyright   : [2016..2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Orphan Elt instances for BigWord and BigInt
--

module Data.Array.Accelerate.Internal.Orphans.Elt (

  pattern W2_,
  pattern I2_,

) where

import Data.Array.Accelerate.Internal.BigInt
import Data.Array.Accelerate.Internal.BigWord

import Data.Array.Accelerate                              hiding ( pattern I2 )


instance (Elt a, Elt b) => Elt (BigWord a b)

pattern W2_ :: (Elt a, Elt b) => Exp a -> Exp b -> Exp (BigWord a b)
pattern W2_ a b = Pattern (a, b)
{-# COMPLETE W2_ #-}

instance (Lift Exp a, Lift Exp b, Elt (Plain a), Elt (Plain b))
    => Lift Exp (BigWord a b) where
  type Plain (BigWord a b) = BigWord (Plain a) (Plain b)
  lift (W2 a b) = W2_ (lift a) (lift b)

instance (Elt a, Elt b) => Unlift Exp (BigWord (Exp a) (Exp b)) where
  unlift (W2_ a b) = W2 a b


instance (Elt a, Elt b) => Elt (BigInt a b)

pattern I2_ :: (Elt a, Elt b) => Exp a -> Exp b -> Exp (BigInt a b)
pattern I2_ a b = Pattern (a, b)
{-# COMPLETE I2_ #-}

instance (Lift Exp a, Lift Exp b, Elt (Plain a), Elt (Plain b))
    => Lift Exp (BigInt a b) where
  type Plain (BigInt a b) = BigInt (Plain a) (Plain b)
  lift (I2 a b)           = I2_ (lift a) (lift b)

instance (Elt a, Elt b) => Unlift Exp (BigInt (Exp a) (Exp b)) where
  unlift (I2_ a b) = I2 a b

