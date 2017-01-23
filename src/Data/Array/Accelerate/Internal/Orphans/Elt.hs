{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Internal.Orphans.Elt
-- Copyright   : [2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Orphan Elt instances for BigWord and BigInt
--

module Data.Array.Accelerate.Internal.Orphans.Elt ()
  where

import Data.Array.Accelerate.Internal.BigInt
import Data.Array.Accelerate.Internal.BigWord

import Data.Array.Accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Smart


type instance EltRepr (BigInt  a b) = EltRepr (a,b)
type instance EltRepr (BigWord a b) = EltRepr (a,b)


instance (Elt a, Elt b, Show (BigWord a b)) => Elt (BigWord a b) where
  eltType _        = eltType (undefined :: (a,b))
  toElt w          = let (a,b) = toElt w in W2 a b
  fromElt (W2 a b) = fromElt (a,b)

instance (cst a, cst b) => IsProduct cst (BigWord a b) where
  type ProdRepr (BigWord a b) = ProdRepr (a,b)
  fromProd cst (W2 a b) = fromProd cst (a,b)
  toProd cst w          = let (a,b) = toProd cst w in W2 a b
  prod cst _            = prod cst (undefined :: (a,b))

instance (Lift Exp a, Lift Exp b, Elt (Plain a), Elt (Plain b), Show (BigWord (Plain a) (Plain b)))
    => Lift Exp (BigWord a b) where
  type Plain (BigWord a b) = BigWord (Plain a) (Plain b)
  lift (W2 a b)            = Exp $ Tuple (NilTup `SnocTup` lift a `SnocTup` lift b)

instance (Elt a, Elt b, Show (BigWord a b)) => Unlift Exp (BigWord (Exp a) (Exp b)) where
  unlift w =
    let a = Exp $ SuccTupIdx ZeroTupIdx `Prj` w
        b = Exp $ ZeroTupIdx `Prj` w
    in
    W2 a b


instance (Elt a, Elt b, Show (BigInt a b)) => Elt (BigInt a b) where
  eltType _        = eltType (undefined :: (a,b))
  toElt w          = let (a,b) = toElt w in I2 a b
  fromElt (I2 a b) = fromElt (a,b)

instance (cst a, cst b) => IsProduct cst (BigInt a b) where
  type ProdRepr (BigInt a b) = ProdRepr (a,b)
  fromProd cst (I2 a b) = fromProd cst (a,b)
  toProd cst w          = let (a,b) = toProd cst w in I2 a b
  prod cst _            = prod cst (undefined :: (a,b))

instance (Lift Exp a, Lift Exp b, Elt (Plain a), Elt (Plain b), Show (BigInt (Plain a) (Plain b)))
    => Lift Exp (BigInt a b) where
  type Plain (BigInt a b) = BigInt (Plain a) (Plain b)
  lift (I2 a b)           = Exp $ Tuple (NilTup `SnocTup` lift a `SnocTup` lift b)

instance (Elt a, Elt b, Show (BigInt a b)) => Unlift Exp (BigInt (Exp a) (Exp b)) where
  unlift w =
    let a = Exp $ SuccTupIdx ZeroTupIdx `Prj` w
        b = Exp $ ZeroTupIdx `Prj` w
    in
    I2 a b

