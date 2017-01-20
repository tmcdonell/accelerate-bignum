{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.Bits
import Data.Int
import Data.Proxy
import Data.Word
import Test.Tasty
import Test.Tasty.QuickCheck                                        hiding ( (.&.) )
import Text.Printf

import Data.Array.Accelerate.Data.BigInt
import Data.Array.Accelerate.Data.BigWord
import Data.Array.Accelerate.Data.Internal.Num2

import Data.Array.Accelerate                                        ( Arrays, Acc, Scalar, Elt, Exp, Lift, Plain )
import Data.Array.Accelerate.Debug                                  ( accInit )
import qualified Data.Array.Accelerate                              as A
import qualified Data.Array.Accelerate.Data.Bits                    as A
import qualified Data.Array.Accelerate.Interpreter                  as I


main :: IO ()
main = do
  accInit
  defaultMain
    $ localOption (QuickCheckTests 10000)
    $ testGroup "accelerate-bignum"
      [ testGroup "base"
        [ testGroup "Num2"
          [ testNum2 (Proxy::Proxy Word8)
          , testNum2 (Proxy::Proxy Word16)
          , testNum2 (Proxy::Proxy Word32)
          , testNum2 (Proxy::Proxy Word64)
          , testNum2 (Proxy::Proxy Int8)
          , testNum2 (Proxy::Proxy Int16)
          , testNum2 (Proxy::Proxy Int32)
          , testNum2 (Proxy::Proxy Int64)
          ]
        , testMain (Proxy::Proxy U64)
        , testMain (Proxy::Proxy I64)
        , testMain (Proxy::Proxy UU64)
        , testMain (Proxy::Proxy II64)
        ]
      , testGroup "accelerate"
        [ testGroup "Num2"
          [ testNum2Acc (Proxy::Proxy Word8)
          , testNum2Acc (Proxy::Proxy Word16)
          , testNum2Acc (Proxy::Proxy Word32)
          , testNum2Acc (Proxy::Proxy Word64)
          , testNum2Acc (Proxy::Proxy Int8)
          , testNum2Acc (Proxy::Proxy Int16)
          , testNum2Acc (Proxy::Proxy Int32)
          , testNum2Acc (Proxy::Proxy Int64)
          ]
        , testGroup "FromIntegral"
          [ testFromIntegral (Proxy::Proxy Int32)  (Proxy::Proxy Int128)
          , testFromIntegral (Proxy::Proxy Int32)  (Proxy::Proxy Int192)
          , testFromIntegral (Proxy::Proxy Int32)  (Proxy::Proxy Word128)
          , testFromIntegral (Proxy::Proxy Int32)  (Proxy::Proxy Word192)
          , testFromIntegral (Proxy::Proxy Int64)  (Proxy::Proxy Int128)
          , testFromIntegral (Proxy::Proxy Int64)  (Proxy::Proxy Int192)
          , testFromIntegral (Proxy::Proxy Int64)  (Proxy::Proxy Word128)
          , testFromIntegral (Proxy::Proxy Int64)  (Proxy::Proxy Word192)
          , testFromIntegral (Proxy::Proxy Word32) (Proxy::Proxy Int128)
          , testFromIntegral (Proxy::Proxy Word32) (Proxy::Proxy Int192)
          , testFromIntegral (Proxy::Proxy Word32) (Proxy::Proxy Word128)
          , testFromIntegral (Proxy::Proxy Word32) (Proxy::Proxy Word192)
          , testFromIntegral (Proxy::Proxy Word64) (Proxy::Proxy Int128)
          , testFromIntegral (Proxy::Proxy Word64) (Proxy::Proxy Int192)
          , testFromIntegral (Proxy::Proxy Word64) (Proxy::Proxy Word128)
          , testFromIntegral (Proxy::Proxy Word64) (Proxy::Proxy Word192)
          ]
        , testMainAcc (Proxy::Proxy Word96)
        , testMainAcc (Proxy::Proxy Word128)
        , testMainAcc (Proxy::Proxy Int96)
        , testMainAcc (Proxy::Proxy Int128)
        ]
      ]

testNum2
    :: (Show (ArgType a), Show a, Num2 a, FiniteBits (Unsigned a), Integral a, Integral (Unsigned a), Bounded a)
    => proxy a
    -> TestTree
testNum2 t = testGroup (showType t)
  [ testProperty "addWithCarry" $ prop_addWithCarry t
  , testProperty "mulWithCarry" $ prop_mulWithCarry t
  ]

testMain
    :: ( Iso a b, Arbitrary a, Show a, Show (ArgType b)
       , Ord a, Bounded a, Real a, Integral a, FiniteBits a
       , Ord b, Bounded b, Real b, Integral b, FiniteBits b
       )
    => proxy b
    -> TestTree
testMain t = testGroup (showType t)
  [ testProperty "iso" $ prop_iso t
  , testGroup "Eq"
    [ testProperty "(==)" $ prop_eq t
    , testProperty "(/=)" $ prop_neq t
    ]
  , testGroup "Ord"
    [ testProperty "compare" $ prop_compare t
    ]
  , testGroup "Bounded"
    [ testProperty "minBound" $ prop_minBound t
    , testProperty "maxBound" $ prop_maxBound t
    ]
  , testGroup "Enum"
    [ testProperty "succ" $ prop_succ t
    , testProperty "pred" $ prop_pred t
    ]
  , testGroup "Num"
    [ testProperty "negate"      $ prop_negate t
    , testProperty "abs"         $ prop_abs t
    , testProperty "signum"      $ prop_signum t
    , testProperty "(+)"         $ prop_add t
    , testProperty "(-)"         $ prop_sub t
    , testProperty "(*)"         $ prop_mul t
    , testProperty "fromInteger" $ prop_fromInteger t
    ]
  , testGroup "Real"
    [ testProperty "toRational" $ prop_toRational t
    ]
  , testGroup "Integral"
    [ testProperty "toInteger" $ prop_toInteger t
    , testProperty "quot"      $ prop_quot t
    , testProperty "rem"       $ prop_rem t
    , testProperty "quotRem"   $ prop_quotRem t
    , testProperty "div"       $ prop_div t
    , testProperty "mod"       $ prop_mod t
    , testProperty "divMod"    $ prop_divMod t
    ]
  , testGroup "Bits"
    [ testProperty "complement"    $ prop_complement t
    , testProperty "xor"           $ prop_xor t
    , testProperty "(.&.)"         $ prop_band t
    , testProperty "(.|.)"         $ prop_bor t
    , testProperty "shiftL"        $ prop_shiftL t
    , testProperty "shiftR"        $ prop_shiftR t
    , testProperty "shift"         $ prop_shift t
    , testProperty "rotateL"       $ prop_rotateL t
    , testProperty "rotateR"       $ prop_rotateR t
    , testProperty "rotate"        $ prop_rotate t
    , testProperty "bit"           $ prop_bit t
    , testProperty "testBit"       $ prop_testBit t
    , testProperty "setBit"        $ prop_setBit t
    , testProperty "clearBit"      $ prop_clearBit t
    , testProperty "complementBit" $ prop_complementBit t
    , testProperty "popCount"      $ prop_popCount t
    ]
  , testGroup "FiniteBits"
    [ testProperty "countLeadingZeros"  $ prop_clz t
    , testProperty "countTrailingZeros" $ prop_ctz t
    ]
  ]

testNum2Acc
    :: ( Show (ArgType a), Bounded a, Integral a, Integral (Unsigned a), FiniteBits (Unsigned a)
       , Elt a, Elt (Unsigned a), Num2 (Exp a)
       , Lift Exp (Unsigned (Exp a)), Plain (Unsigned (Exp a)) ~ Unsigned a
       )
    => proxy a
    -> TestTree
testNum2Acc t = testGroup (showType t)
  [ testProperty "addWithCarry" $ prop_addWithCarry' t
  , testProperty "mulWithCarry" $ prop_mulWithCarry' t
  ]

testFromIntegral
    :: (Show (ArgType a), Show (ArgType b), Arbitrary a, Integral a, Num b, Eq b, A.Integral a, A.Num b, A.FromIntegral a b)
    => proxy a
    -> proxy b
    -> TestTree
testFromIntegral ta tb =
  testProperty (printf "%s->%s" (showType ta) (showType tb)) $ prop_fromIntegral ta tb

testMainAcc
    :: ( Arbitrary a, Show (ArgType a)
       ,   Ord a,   Integral a,   Bounded a,   FiniteBits a
       , A.Ord a, A.Integral a, A.Bounded a, A.FiniteBits a
       )
    => proxy a
    -> TestTree
testMainAcc t = testGroup (showType t)
  [ testGroup "Eq"
    [ testProperty "(==)" $ prop_eq' t
    , testProperty "(/=)" $ prop_neq' t
    ]
  , testGroup "Ord"
    [ testProperty "(<)"  $ prop_lt' t
    , testProperty "(>)"  $ prop_gt' t
    , testProperty "(<=)" $ prop_lte' t
    , testProperty "(>=)" $ prop_gte' t
    ]
  , testGroup "Bounded"
    [ testProperty "minBound" $ prop_minBound' t
    , testProperty "maxBound" $ prop_maxBound' t
    ]
  , testGroup "Num"
    [ testProperty "negate"      $ prop_negate' t
    , testProperty "abs"         $ prop_abs' t
    , testProperty "signum"      $ prop_signum' t
    , testProperty "(+)"         $ prop_add' t
    , testProperty "(-)"         $ prop_sub' t
    , testProperty "(*)"         $ prop_mul' t
    , testProperty "fromInteger" $ prop_fromInteger' t
    ]
  , testGroup "Integral"
    [ testProperty "quot"    $ prop_quot' t
    , testProperty "rem"     $ prop_rem' t
    , testProperty "quotRem" $ prop_quotRem' t
    , testProperty "div"     $ prop_div' t
    , testProperty "mod"     $ prop_mod' t
    , testProperty "divMod"  $ prop_divMod' t
    ]
  , testGroup "Bits"
    [ testProperty "complement"    $ prop_complement' t
    , testProperty "xor"           $ prop_xor' t
    , testProperty "(.&.)"         $ prop_band' t
    , testProperty "(.|.)"         $ prop_bor' t
    , testProperty "shiftL"        $ prop_shiftL' t
    , testProperty "shiftR"        $ prop_shiftR' t
    , testProperty "shift"         $ prop_shift' t
    , testProperty "rotateL"       $ prop_rotateL' t
    , testProperty "rotateR"       $ prop_rotateR' t
    , testProperty "rotate"        $ prop_rotate' t
    , testProperty "bit"           $ prop_bit' t
    , testProperty "testBit"       $ prop_testBit' t
    , testProperty "setBit"        $ prop_setBit' t
    , testProperty "clearBit"      $ prop_clearBit' t
    , testProperty "complementBit" $ prop_complementBit' t
    , testProperty "popCount"      $ prop_popCount' t
    ]
  , testGroup "FiniteBits"
    [ testProperty "countLeadingZeros"  $ prop_clz' t
    , testProperty "countTrailingZeros" $ prop_ctz' t
    ]
  ]


prop_addWithCarry, prop_mulWithCarry :: (Num2 a, Integral a, FiniteBits (Unsigned a), Integral (Unsigned a)) => proxy a -> Large a -> Large a -> Bool
prop_addWithCarry _ (Large x) (Large y) = uncurry toInteger2 (addWithCarry x y) == toInteger x + toInteger y
prop_mulWithCarry _ (Large x) (Large y) = uncurry toInteger2 (mulWithCarry x y) == toInteger x * toInteger y

toInteger2 :: (Integral a, Integral b, FiniteBits b) => a -> b -> Integer
toInteger2 h l = toInteger h * 2 ^ finiteBitSize l + toInteger l

prop_iso :: (Iso a b, Eq a) => proxy b -> a -> Bool
prop_iso t x = isoL (toIso t x) == x

prop_eq, prop_neq :: (Iso a b, Eq a, Eq b) => proxy b -> a -> a -> Bool
prop_eq   = prop_binary' (==) (==)
prop_neq  = prop_binary' (/=) (/=)

prop_compare :: (Iso a b, Ord a, Ord b) => proxy b -> a -> a -> Bool
prop_compare = prop_binary' compare compare

prop_minBound, prop_maxBound :: (Iso a b, Bounded a, Bounded b, Eq a) => proxy b -> Bool
prop_minBound t = minBound == fromIso t minBound
prop_maxBound t = maxBound == fromIso t maxBound

prop_succ, prop_pred :: (Bounded a, Enum a, Enum b, Eq a, Iso a b) => proxy b -> a -> Property
prop_succ t x = (x /= maxBound) ==> (succ x == with_unary t succ x)
prop_pred t x = (x /= minBound) ==> (pred x == with_unary t pred x)

prop_negate, prop_abs, prop_signum :: (Iso a b, Num a, Num b, Eq a) => proxy b -> a -> Bool
prop_negate = prop_unary negate negate
prop_abs    = prop_unary abs abs
prop_signum = prop_unary signum signum

prop_add, prop_sub, prop_mul :: (Iso a b, Num a, Num b, Eq a) => proxy b -> a -> a -> Bool
prop_add    = prop_binary (+) (+)
prop_sub    = prop_binary (-) (-)
prop_mul    = prop_binary (*) (*)

prop_fromInteger :: (Iso a b, Num a, Eq a, Num b) => proxy b -> Integer -> Bool
prop_fromInteger t x = fromInteger x == fromIso t (fromInteger x)

prop_toRational :: (Iso a b, Real a, Real b) => proxy b -> a -> Bool
prop_toRational = prop_unary' toRational toRational

prop_toInteger :: (Iso a b, Integral a, Integral b) => proxy b -> a -> Bool
prop_toInteger = prop_unary' toInteger toInteger

prop_quot, prop_rem, prop_div, prop_mod :: (Iso a b, Integral a, Integral b) => proxy b -> a -> NonZero a -> Bool
prop_quot t x (NonZero y) = prop_binary quot quot t x y
prop_rem  t x (NonZero y) = prop_binary rem  rem  t x y
prop_div  t x (NonZero y) = prop_binary div  div  t x y
prop_mod  t x (NonZero y) = prop_binary mod  mod  t x y

prop_quotRem :: (Iso a b, Integral a, Integral b) => proxy b -> a -> NonZero a -> Bool
prop_quotRem  t x (NonZero y) =
  let qr    = quotRem x y
      (q,r) = quotRem (toIso t x) (toIso t y)
  in
  qr == (fromIso t q, fromIso t r)

prop_divMod :: (Iso a b, Integral a, Integral b) => proxy b -> a -> NonZero a -> Bool
prop_divMod  t x (NonZero y) =
  let qr    = divMod x y
      (q,r) = divMod (toIso t x) (toIso t y)
  in
  qr == (fromIso t q, fromIso t r)

prop_complement :: (Iso a b, Bits a, Bits b) => proxy b -> a -> Bool
prop_complement = prop_unary complement complement

prop_xor, prop_band, prop_bor :: (Iso a b, Bits a, Bits b) => proxy b -> a -> a -> Bool
prop_xor  = prop_binary xor xor
prop_band = prop_binary (.&.) (.&.)
prop_bor  = prop_binary (.|.) (.|.)

prop_shiftL, prop_shiftR, prop_rotateL, prop_rotateR :: (Iso a b, FiniteBits a, FiniteBits b) => proxy b -> a -> NonNegative Int -> Property
prop_shiftL  t x (NonNegative n) = n < finiteBitSize x ==> prop_unary (`shiftL` n) (`shiftL` n) t x
prop_shiftR  t x (NonNegative n) = n < finiteBitSize x ==> prop_unary (`shiftR` n) (`shiftR` n) t x
prop_rotateL t x (NonNegative n) = n < finiteBitSize x ==> prop_unary (`rotateL` n) (`rotateL` n) t x
prop_rotateR t x (NonNegative n) = n < finiteBitSize x ==> prop_unary (`rotateR` n) (`rotateR` n) t x

prop_shift, prop_rotate :: (Iso a b, FiniteBits a, FiniteBits b) => proxy b -> a -> Int -> Property
prop_shift  t x n = abs n < finiteBitSize x ==> prop_unary (`shift` n) (`shift` n) t x
prop_rotate t x n = abs n < finiteBitSize x ==> prop_unary (`rotate` n) (`rotate` n) t x

prop_bit :: forall proxy a b. (Iso a b, FiniteBits a, FiniteBits b) => proxy b -> Bool
prop_bit t = all (\b -> bit b == fromIso t (bit b)) [0 .. finiteBitSize (undefined::a) - 1]

prop_testBit, prop_setBit, prop_clearBit, prop_complementBit :: (Iso a b, FiniteBits a, FiniteBits b) => proxy b -> a -> NonNegative Int -> Property
prop_testBit       t x (NonNegative n) = n < finiteBitSize x ==> prop_unary' (`testBit` n) (`testBit` n) t x
prop_setBit        t x (NonNegative n) = n < finiteBitSize x ==> prop_unary (`setBit` n) (`setBit` n) t x
prop_clearBit      t x (NonNegative n) = n < finiteBitSize x ==> prop_unary (`clearBit` n) (`clearBit` n) t x
prop_complementBit t x (NonNegative n) = n < finiteBitSize x ==> prop_unary (`complementBit` n) (`complementBit` n) t x

prop_popCount :: (Iso a b, FiniteBits a, FiniteBits b) => proxy b -> a -> Bool
prop_popCount = prop_unary' popCount popCount

prop_clz, prop_ctz :: (Iso a b, FiniteBits a, FiniteBits b) => proxy b -> a -> Bool
prop_clz = prop_unary' countLeadingZeros countLeadingZeros
prop_ctz = prop_unary' countTrailingZeros countTrailingZeros


fromIso :: Iso a b => proxy b -> b -> a
fromIso _ = isoL

toIso :: Iso a b => proxy b -> a -> b
toIso _ = isoR

with_unary :: Iso a b => proxy b -> (b -> b) -> a -> a
with_unary _ f = isoL . f . isoR

with_unary' :: Iso a b => proxy b -> (b -> r) -> a -> r
with_unary' _ f x = f (isoR x)

prop_unary :: (Iso a b, Eq a) => (a -> a) -> (b -> b) -> proxy b -> a -> Bool
prop_unary f g p x = f x == with_unary p g x

prop_unary' :: (Iso a b, Eq r) => (a -> r) -> (b -> r) -> proxy b -> a -> Bool
prop_unary' f g p x = f x == with_unary' p g x

prop_binary :: (Iso a b, Eq a) => (a -> a -> a) -> (b -> b -> b) -> proxy b -> a -> a -> Bool
prop_binary f g p x y = f x y == with_binary p g x y

with_binary :: Iso a b => proxy b -> (b -> b -> b) -> a -> a -> a
with_binary _ f x y = isoL $ f (isoR x) (isoR y)

with_binary' :: Iso a b => proxy b -> (b -> b -> r) -> a -> a -> r
with_binary' _ f x y = f (isoR x) (isoR y)

prop_binary' :: (Iso a b, Eq r) => (a -> a -> r) -> (b -> b -> r) -> proxy b -> a -> a -> Bool
prop_binary'  f g p x y = f x y == with_binary' p g x y


type I64  = BigInt  Int32  Word32
type U64  = BigWord Word32 Word32

type II64 = BigInt  Int16  (BigWord Word16 Word32)
type UU64 = BigWord Word16 (BigWord Word16 Word32)

class Iso a b | b -> a where
  isoR :: a -> b
  isoL :: b -> a

instance Iso Word64 U64 where
  isoR w        = W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w)
  isoL (W2 h l) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Word64 UU64 where
  isoR w                 = W2 (fromIntegral (w `shiftR` 48)) (W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w))
  isoL (W2 h (W2 lh ll)) =  fromIntegral h  `shiftL` 48
                        .|. fromIntegral lh `shiftL` 32
                        .|. fromIntegral ll

instance Iso Int64 I64 where
  isoR w        = I2 (fromIntegral (w `shiftR` 32)) (fromIntegral w)
  isoL (I2 h l) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Int64 II64 where
  isoR w                 = I2 (fromIntegral (w `shiftR` 48)) (W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w))
  isoL (I2 h (W2 lh ll)) =  fromIntegral h  `shiftL` 48
                        .|. fromIntegral lh `shiftL` 32
                        .|. fromIntegral ll

instance Elt a => Iso a (Scalar a) where
  isoR x = A.fromList A.Z [x]
  isoL x = A.indexArray x A.Z

instance (Arbitrary a, Arbitrary b) => Arbitrary (BigWord a b) where
  arbitrary         = W2 <$> arbitrary <*> arbitrary
  shrink (W2 hi lo) = [ W2 hi' lo' | (hi',lo') <- shrink (hi,lo) ]

instance (Arbitrary a, Arbitrary b) => Arbitrary (BigInt a b) where
  arbitrary         = I2 <$> arbitrary <*> arbitrary
  shrink (I2 hi lo) = [ I2 hi' lo' | (hi',lo') <- shrink (hi,lo) ]


{-# INLINE prop_unary_acc #-}
prop_unary_acc :: (Elt a, Elt r, Eq r) => (a -> r) -> (Exp a -> Exp r) -> proxy a -> a -> Bool
prop_unary_acc f g p x = f x == with_unary_acc p g x

{-# INLINE prop_binary_acc #-}
prop_binary_acc :: (Elt a, Elt r, Eq r) => (a -> a -> r) -> (Exp a -> Exp a -> Exp r) -> proxy a -> a -> a -> Bool
prop_binary_acc f g p x y = f x y == with_binary_acc p g x y

{-# INLINE prop_binary_acc' #-}
prop_binary_acc' :: (Elt a, Elt r, Eq r) => (a -> Int -> r) -> (Exp a -> Exp Int -> Exp r) -> proxy a -> a -> Int -> Bool
prop_binary_acc' f g p x y = f x y == with_binary_acc' p g x y

-- TLM: make sure to pass the operation though a 'run', otherwise the expression
--      will be constant-folded away before hitting the backend.
--
{-# INLINE with_unary_acc #-}
with_unary_acc :: forall proxy a r. (Elt a, Elt r) => proxy a -> (Exp a -> Exp r) -> a -> r
with_unary_acc _ f = isoL . f' . isoR
  where
    f' :: Scalar a -> Scalar r
    !f' = I.run1 (A.map f)

{-# INLINE with_binary_acc #-}
with_binary_acc :: forall proxy a r. (Elt a, Elt r) => proxy a -> (Exp a -> Exp a -> Exp r) -> a -> a -> r
with_binary_acc _ f x y = isoL $ f' (isoR x) (isoR y)
  where
    f' :: Scalar a -> Scalar a -> Scalar r
    !f' = run2 (A.zipWith f)

{-# INLINE with_binary_acc' #-}
with_binary_acc' :: forall proxy a r. (Elt a, Elt r) => proxy a -> (Exp a -> Exp Int -> Exp r) -> a -> Int -> r
with_binary_acc' _ f x y = isoL $ f' (isoR x) (isoR y)
  where
    f' :: Scalar a -> Scalar Int -> Scalar r
    !f' = run2 (A.zipWith f)

{-# INLINE run2 #-}
run2 :: (Arrays a, Arrays b, Arrays c) => (Acc a -> Acc b -> Acc c) -> a -> b -> c
run2 f x y = go (x,y)
  where
    !go = I.run1 (A.uncurry f)

infixr 0 $$
($$) :: (b -> a) -> (c -> d -> b) -> c -> d -> a
(f $$ g) x y = f (g x y)


prop_addWithCarry', prop_mulWithCarry'
    :: (Num2 (Exp a), Elt a, Elt (Unsigned a), Integral a, Integral (Unsigned a), FiniteBits (Unsigned a), A.Lift Exp (Unsigned (Exp a)), Plain (Unsigned (Exp a)) ~ Unsigned a)
    => proxy a
    -> Large a
    -> Large a
    -> Bool
prop_addWithCarry' t (Large x) (Large y) = uncurry toInteger2 (with_binary_acc t (A.lift $$ addWithCarry) x y) == toInteger x + toInteger y
prop_mulWithCarry' t (Large x) (Large y) = uncurry toInteger2 (with_binary_acc t (A.lift $$ mulWithCarry) x y) == toInteger x * toInteger y

prop_fromIntegral
    :: forall proxy a b. (Integral a, Num b, Eq b, A.Integral a, A.Num b, A.FromIntegral a b)
    => proxy a
    -> proxy b
    -> a
    -> Bool
prop_fromIntegral a _ = prop_unary_acc fromIntegral (A.fromIntegral :: Exp a -> Exp b) a

prop_eq', prop_neq' :: (Eq a, A.Eq a) => proxy a -> a -> a -> Bool
prop_eq'  = prop_binary_acc (==) (A.==)
prop_neq' = prop_binary_acc (/=) (A./=)

prop_lt', prop_lte', prop_gt', prop_gte' :: (Ord a, A.Ord a) => proxy a -> a -> a -> Bool
prop_lt'  = prop_binary_acc (<)  (A.<)
prop_gt'  = prop_binary_acc (>)  (A.>)
prop_lte' = prop_binary_acc (<=) (A.<=)
prop_gte' = prop_binary_acc (>=) (A.>=)

prop_minBound', prop_maxBound' :: forall proxy a. (Bounded a, Eq a, A.Bounded a) => proxy a -> Bool
prop_minBound' _ = minBound == isoL (I.run (A.unit (minBound :: Exp a)))
prop_maxBound' _ = maxBound == isoL (I.run (A.unit (maxBound :: Exp a)))

prop_negate', prop_abs', prop_signum' :: (Num a, A.Num a, Eq a) => proxy a -> a -> Bool
prop_negate' = prop_unary_acc negate negate
prop_abs'    = prop_unary_acc abs abs
prop_signum' = prop_unary_acc signum signum

prop_add', prop_sub', prop_mul' :: (Num a, A.Num a, Eq a) => proxy a -> a -> a -> Bool
prop_add'    = prop_binary_acc (+) (+)
prop_sub'    = prop_binary_acc (-) (-)
prop_mul'    = prop_binary_acc (*) (*)

prop_fromInteger' :: forall proxy a. (Num a, Eq a, A.Num a) => proxy a -> Integer -> Bool
prop_fromInteger' _ x = fromInteger x == isoL (I.run (A.unit (fromInteger x :: Exp a)))

prop_quot', prop_rem', prop_div', prop_mod', prop_quotRem', prop_divMod' :: (Integral a, A.Integral a) => proxy a -> a -> NonZero a -> Bool
prop_quot'    t x (NonZero y) = prop_binary_acc quot quot t x y
prop_rem'     t x (NonZero y) = prop_binary_acc rem  rem  t x y
prop_div'     t x (NonZero y) = prop_binary_acc div  div  t x y
prop_mod'     t x (NonZero y) = prop_binary_acc mod  mod  t x y
prop_quotRem' t x (NonZero y) = prop_binary_acc quotRem (A.lift $$ quotRem) t x y
prop_divMod'  t x (NonZero y) = prop_binary_acc divMod  (A.lift $$ divMod)  t x y

prop_complement' :: (Bits a, A.Bits a) => proxy a -> a -> Bool
prop_complement' = prop_unary_acc complement A.complement

prop_xor', prop_band', prop_bor' :: (Bits a, A.Bits a) => proxy a -> a -> a -> Bool
prop_xor'  = prop_binary_acc xor A.xor
prop_band' = prop_binary_acc (.&.) (A..&.)
prop_bor'  = prop_binary_acc (.|.) (A..|.)

prop_shiftL', prop_shiftR', prop_rotateL', prop_rotateR' :: (FiniteBits a, A.FiniteBits a) => proxy a -> a -> NonNegative Int -> Property
prop_shiftL'  t x (NonNegative n) = n < finiteBitSize x ==> prop_binary_acc' shiftL A.shiftL t x n
prop_shiftR'  t x (NonNegative n) = n < finiteBitSize x ==> prop_binary_acc' shiftR A.shiftR t x n
prop_rotateL' t x (NonNegative n) = n < finiteBitSize x ==> prop_binary_acc' rotateL A.rotateL t x n
prop_rotateR' t x (NonNegative n) = n < finiteBitSize x ==> prop_binary_acc' rotateR A.rotateR t x n

prop_shift', prop_rotate' :: (FiniteBits a, A.FiniteBits a) => proxy a -> a -> Int -> Property
prop_shift'  t x n = abs n < finiteBitSize x ==> prop_binary_acc' shift A.shift t x n
prop_rotate' t x n = abs n < finiteBitSize x ==> prop_binary_acc' rotate A.rotate t x n

prop_bit' :: forall proxy a. (FiniteBits a, A.FiniteBits a) => proxy a -> Bool
prop_bit' _ = all (prop_unary_acc (bit :: Int -> a) A.bit Proxy) [0 .. finiteBitSize (undefined::a) - 1]

prop_testBit', prop_setBit', prop_clearBit', prop_complementBit' :: (FiniteBits a, A.FiniteBits a) => proxy a -> a -> NonNegative Int -> Property
prop_testBit'       t x (NonNegative n) = n < finiteBitSize x ==> prop_binary_acc' testBit A.testBit t x
prop_setBit'        t x (NonNegative n) = n < finiteBitSize x ==> prop_binary_acc' setBit A.setBit t x
prop_clearBit'      t x (NonNegative n) = n < finiteBitSize x ==> prop_binary_acc' clearBit A.clearBit t x
prop_complementBit' t x (NonNegative n) = n < finiteBitSize x ==> prop_binary_acc' complementBit A.complementBit t x

prop_popCount' :: (FiniteBits a, A.FiniteBits a) => proxy a -> a -> Bool
prop_popCount' = prop_unary_acc popCount A.popCount

prop_clz', prop_ctz' :: (FiniteBits a, A.FiniteBits a) => proxy a -> a -> Bool
prop_clz' = prop_unary_acc countLeadingZeros  A.countLeadingZeros
prop_ctz' = prop_unary_acc countTrailingZeros A.countTrailingZeros


data ArgType (a :: *) = AT

showType :: forall proxy a. Show (ArgType a) => proxy a -> String
showType _ = show (AT :: ArgType a)

instance FiniteBits (BigWord a b) => Show (ArgType (BigWord a b)) where
  show _ = printf "Word%d" (finiteBitSize (undefined::BigWord a b))

instance FiniteBits (BigInt a b) => Show (ArgType (BigInt a b)) where
  show _ = printf "Int%d" (finiteBitSize (undefined::BigInt a b))

instance Show (ArgType Int8)   where show _ = "Int8"
instance Show (ArgType Int16)  where show _ = "Int16"
instance Show (ArgType Int32)  where show _ = "Int32"
instance Show (ArgType Int64)  where show _ = "Int64"
instance Show (ArgType Word8)  where show _ = "Word8"
instance Show (ArgType Word16) where show _ = "Word16"
instance Show (ArgType Word32) where show _ = "Word32"
instance Show (ArgType Word64) where show _ = "Word64"

