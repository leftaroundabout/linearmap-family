-- |
-- Module      : Math.LinearMap.Category.Instances
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TupleSections              #-}

module Math.LinearMap.Category.Instances where

import Math.LinearMap.Category.Class

import Data.VectorSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion

import Data.Foldable (foldl')

import Data.VectorSpace.Free
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import qualified Linear.Metric as Mat
import Linear (_x, _y, _z, _w)
import Control.Lens ((^.))

import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional


type ℝ = Double

instance TensorSpace ℝ where
  type TensorProduct ℝ w = w
  zeroTensor = Tensor zeroV
  scaleTensor = LinearFunction (pretendLike Tensor) . scale
  addTensors (Tensor v) (Tensor w) = Tensor $ v ^+^ w
  subtractTensors (Tensor v) (Tensor w) = Tensor $ v ^-^ w
  negateTensor = pretendLike Tensor lNegateV
  toFlatTensor = follow Tensor
  fromFlatTensor = flout Tensor
  tensorProduct = LinearFunction $ \μ -> follow Tensor . scaleWith μ
  transposeTensor = toFlatTensor . flout Tensor
  fmapTensor = LinearFunction $ pretendLike Tensor
  fzipTensorWith = LinearFunction
                   $ \f -> follow Tensor <<< f <<< flout Tensor *** flout Tensor
  coerceFmapTensorProduct _ Coercion = Coercion
instance LinearSpace ℝ where
  type DualVector ℝ = ℝ
  linearId = LinearMap 1
  idTensor = Tensor 1
  fromLinearForm = flout LinearMap
  coerceDoubleDual = Coercion
  contractTensorMap = flout Tensor . flout LinearMap
  contractMapTensor = flout LinearMap . flout Tensor
  contractTensorWith = flout Tensor >>> applyDualVector
  contractLinearMapAgainst = flout LinearMap >>> flipBilin lApply
  blockVectSpan = follow Tensor . follow LinearMap
  applyDualVector = scale
  applyLinear = elacs . flout LinearMap
  composeLinear = LinearFunction $ \f -> follow LinearMap . arr f . flout LinearMap

#define FreeLinearSpace(V, LV, tp, bspan, tenspl, dspan, contraction, contraaction)                                  \
instance Num''' s => TensorSpace (V s) where {                     \
  type TensorProduct (V s) w = V w;                               \
  zeroTensor = Tensor $ pure zeroV;                                \
  addTensors (Tensor m) (Tensor n) = Tensor $ liftA2 (^+^) m n;     \
  subtractTensors (Tensor m) (Tensor n) = Tensor $ liftA2 (^-^) m n; \
  negateTensor = LinearFunction $ Tensor . fmap negateV . getTensorProduct;  \
  scaleTensor = bilinearFunction   \
          $ \μ -> Tensor . fmap (μ*^) . getTensorProduct; \
  toFlatTensor = follow Tensor; \
  fromFlatTensor = flout Tensor; \
  tensorProduct = bilinearFunction $ \w v -> Tensor $ fmap (*^v) w; \
  transposeTensor = LinearFunction (tp); \
  fmapTensor = bilinearFunction $       \
          \(LinearFunction f) -> pretendLike Tensor $ fmap f; \
  fzipTensorWith = bilinearFunction $ \
          \(LinearFunction f) (Tensor vw, Tensor vx) \
                  -> Tensor $ liftA2 (curry f) vw vx; \
  coerceFmapTensorProduct _ Coercion = Coercion };                  \
instance Num''' s => LinearSpace (V s) where {                  \
  type DualVector (V s) = V s;                                 \
  linearId = LV Mat.identity;                                   \
  idTensor = Tensor Mat.identity; \
  coerceDoubleDual = Coercion; \
  fromLinearForm = flout LinearMap; \
  blockVectSpan = LinearFunction $ Tensor . (bspan);            \
  contractTensorMap = LinearFunction $ (contraction) . coerce . getLinearMap;      \
  contractMapTensor = LinearFunction $ (contraction) . coerce . getTensorProduct;      \
  contractTensorWith = bilinearFunction $ \
             \(Tensor wv) dw -> fmap (arr $ applyDualVector $ dw) wv;      \
  contractLinearMapAgainst = bilinearFunction $ getLinearMap >>> (contraaction); \
  applyDualVector = bilinearFunction Mat.dot;           \
  applyLinear = bilinearFunction $ \(LV m)                        \
                  -> foldl' (^+^) zeroV . liftA2 (^*) m;           \
  composeLinear = bilinearFunction $   \
         \f (LinearMap g) -> LinearMap $ fmap (f$) g }
FreeLinearSpace( V0
               , LinearMap
               , \(Tensor V0) -> zeroV
               , \_ -> V0
               , \_ -> LinearMap V0
               , LinearMap V0
               , \V0 -> zeroV
               , \V0 _ -> 0 )
FreeLinearSpace( V1
               , LinearMap
               , \(Tensor (V1 w₀)) -> w₀⊗V1 1
               , \w -> V1 (LinearMap $ V1 w)
               , \w -> LinearMap $ V1 (Tensor $ V1 w)
               , LinearMap . V1 . blockVectSpan $ V1 1
               , \(V1 (V1 w)) -> w
               , \(V1 x) f -> (f$x)^._x )
FreeLinearSpace( V2
               , LinearMap
               , \(Tensor (V2 w₀ w₁)) -> w₀⊗V2 1 0
                                     ^+^ w₁⊗V2 0 1
               , \w -> V2 (LinearMap $ V2 w zeroV)
                          (LinearMap $ V2 zeroV w)
               , \w -> LinearMap $ V2 (Tensor $ V2 w zeroV)
                                      (Tensor $ V2 zeroV w)
               , LinearMap $ V2 (blockVectSpan $ V2 1 0)
                                (blockVectSpan $ V2 0 1)
               , \(V2 (V2 w₀ _)
                      (V2 _ w₁)) -> w₀^+^w₁
               , \(V2 x y) f -> (f$x)^._x + (f$y)^._y )
FreeLinearSpace( V3
               , LinearMap
               , \(Tensor (V3 w₀ w₁ w₂)) -> w₀⊗V3 1 0 0
                                        ^+^ w₁⊗V3 0 1 0
                                        ^+^ w₂⊗V3 0 0 1
               , \w -> V3 (LinearMap $ V3 w zeroV zeroV)
                          (LinearMap $ V3 zeroV w zeroV)
                          (LinearMap $ V3 zeroV zeroV w)
               , \w -> LinearMap $ V3 (Tensor $ V3 w zeroV zeroV)
                                      (Tensor $ V3 zeroV w zeroV)
                                      (Tensor $ V3 zeroV zeroV w)
               , LinearMap $ V3 (blockVectSpan $ V3 1 0 0)
                                (blockVectSpan $ V3 0 1 0)
                                (blockVectSpan $ V3 0 0 1)
               , \(V3 (V3 w₀ _ _)
                      (V3 _ w₁ _)
                      (V3 _ _ w₂)) -> w₀^+^w₁^+^w₂
               , \(V3 x y z) f -> (f$x)^._x + (f$y)^._y + (f$z)^._z )
FreeLinearSpace( V4
               , LinearMap
               , \(Tensor (V4 w₀ w₁ w₂ w₃)) -> w₀⊗V4 1 0 0 0
                                           ^+^ w₁⊗V4 0 1 0 0
                                           ^+^ w₂⊗V4 0 0 1 0
                                           ^+^ w₃⊗V4 0 0 0 1
               , \w -> V4 (LinearMap $ V4 w zeroV zeroV zeroV)
                          (LinearMap $ V4 zeroV w zeroV zeroV)
                          (LinearMap $ V4 zeroV zeroV w zeroV)
                          (LinearMap $ V4 zeroV zeroV zeroV w)
               , \w -> LinearMap $ V4 (Tensor $ V4 w zeroV zeroV zeroV)
                                      (Tensor $ V4 zeroV w zeroV zeroV)
                                      (Tensor $ V4 zeroV zeroV w zeroV)
                                      (Tensor $ V4 zeroV zeroV zeroV w)
               , LinearMap $ V4 (blockVectSpan $ V4 1 0 0 0)
                                (blockVectSpan $ V4 0 1 0 0)
                                (blockVectSpan $ V4 0 0 1 0)
                                (blockVectSpan $ V4 0 0 0 1)
               , \(V4 (V4 w₀ _ _ _)
                      (V4 _ w₁ _ _)
                      (V4 _ _ w₂ _)
                      (V4 _ _ _ w₃)) -> w₀^+^w₁^+^w₂^+^w₃
               , \(V4 x y z w) f -> (f$x)^._x + (f$y)^._y + (f$z)^._z + (f$w)^._w )




  

