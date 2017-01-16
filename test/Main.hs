{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Main where

import Data.Proxy
import Data.Typeable
import Data.Word
import Data.Bits
import Test.Tasty
import Test.Tasty.QuickCheck                                        hiding ( (.&.) )

import Data.Array.Accelerate.Data.BigWord


main :: IO ()
main
  = defaultMain
  $ localOption (QuickCheckTests 10000)
  $ testGroup "accelerate-bignum"
    [ testAll (Proxy::Proxy U64)
    , testAll (Proxy::Proxy UU64)
    ]


testAll
    :: forall proxy a b.
       ( Iso a b, Arbitrary a, Typeable b, Show a
       , Eq a, Ord a, Bounded a, Enum a, Num a, Real a, Integral a, FiniteBits a
       , Eq b, Ord b, Bounded b, Enum b, Num b, Real b, Integral b, FiniteBits b
       )
    => proxy b
    -> TestTree
testAll t = testGroup (show (typeRep t))
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
prop_abs    = prop_unary negate negate
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

prop_quot, prop_rem, prop_div, prop_mod :: (Iso a b, Integral a, Integral b) => proxy b -> a -> a -> Property
prop_quot t x y = y /= 0 ==> prop_binary quot quot t x y
prop_rem  t x y = y /= 0 ==> prop_binary rem  rem  t x y
prop_div  t x y = y /= 0 ==> prop_binary div  div  t x y
prop_mod  t x y = y /= 0 ==> prop_binary mod  mod  t x y

prop_quotRem :: (Iso a b, Integral a, Integral b) => proxy b -> a -> a -> Property
prop_quotRem  t x y = y /= 0 ==>
  let qr    = quotRem x y
      (q,r) = quotRem (toIso t x) (toIso t y)
  in
  qr == (fromIso t q, fromIso t r)

prop_divMod :: (Iso a b, Integral a, Integral b) => proxy b -> a -> a -> Property
prop_divMod  t x y = y /= 0 ==>
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


type U64  = BigWord Word32 Word32
type UU64 = BigWord Word16 (BigWord Word16 Word32)

class Iso a b | b -> a where
  isoR :: a -> b
  isoL :: b -> a

instance Iso Word64 U64 where
  isoR w        = W2 (fromIntegral (w `shiftR` 32)) (fromIntegral w)
  isoL (W2 h l) = fromIntegral h `shiftL` 32 .|. fromIntegral l

instance Iso Word64 UU64 where
  isoR w                 = W2 (fromIntegral $ w `shiftR` 48) (W2 (fromIntegral $ w `shiftR` 32) (fromIntegral w))
  isoL (W2 h (W2 lh ll)) =  fromIntegral h  `shiftL` 48
                        .|. fromIntegral lh `shiftL` 32
                        .|. fromIntegral ll

