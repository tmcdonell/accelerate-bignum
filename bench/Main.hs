{-# LANGUAGE CPP #-}

module Main where

import Control.Applicative
import Criterion.Main
import Data.Maybe
import Data.Vector.Unboxed                                          ( Vector )
import Data.Word
import System.Random.MWC
import qualified Data.Vector.Unboxed                                as U
import Prelude                                                      as P

import qualified WideWord
import qualified Accelerate
#if ACCELERATE_LLVM_NATIVE_BACKEND
import qualified Data.Array.Accelerate.LLVM.Native                  as CPU
#endif
#if ACCELERATE_LLVM_PTX_BACKEND
import qualified Data.Array.Accelerate.LLVM.PTX                     as PTX
#endif


lIMIT :: Int
lIMIT = 1000000

generateData :: IO (Vector Word64, Vector Word64, Vector Word64, Vector Word64, Vector Int)
generateData =
  withSystemRandom . asGenIO $ \gen ->
    (,,,,) <$> uniformVector gen lIMIT
           <*> uniformVector gen lIMIT
           <*> uniformVector gen lIMIT
           <*> uniformVector gen lIMIT
           <*> U.replicateM lIMIT (uniformR (-64,64) gen)

main :: IO ()
main = do
  (xh,xl,yh,yl,ss) <- generateData
  defaultMain
    [ WideWord.benchmark xh xl yh yl ss
    , bgroup "accelerate"
    $ catMaybes
      [ Nothing
#if ACCELERATE_LLVM_NATIVE_BACKEND
      , Just $ Accelerate.benchmark "llvm-cpu" CPU.run1 xh xl yh yl ss
#endif
#if ACCELERATE_LLVM_PTX_BACKEND
      , Just $ Accelerate.benchmark "llvm-ptx" PTX.run1 xh xl yh yl ss
#endif
      ]
    ]

