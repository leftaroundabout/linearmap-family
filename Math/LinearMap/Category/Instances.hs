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

import Math.Manifold.Core.PseudoAffine

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion
import Data.Tagged

import Data.Foldable (foldl')

import Data.VectorSpace.Free
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import qualified Linear.Metric as Mat
import Linear ( V0(V0), V1(V1), V2(V2), V3(V3), V4(V4)
              , _x, _y, _z, _w )
import Control.Lens ((^.))

import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional


infixr 7 <.>^
(<.>^) :: LinearSpace v => DualVector v -> v -> Scalar v
f<.>^v = (applyDualVector-+$>f)-+$>v


type ℝ = Double

instance Num' ℝ where
  closedScalarWitness = ClosedScalarWitness

instance TensorSpace ℝ where
  type TensorProduct ℝ w = w
  scalarSpaceWitness = ScalarSpaceWitness
  linearManifoldWitness = LinearManifoldWitness BoundarylessWitness
  zeroTensor = Tensor zeroV
  scaleTensor = bilinearFunction $ \μ (Tensor t) -> Tensor $ μ*^t
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
  dualSpaceWitness = DualSpaceWitness
  linearId = LinearMap 1
  tensorId = uncurryLinearMap $ LinearMap $ fmap (follow Tensor) -+$> id
  idTensor = Tensor 1
  fromLinearForm = flout LinearMap
  coerceDoubleDual = Coercion
  contractTensorMap = flout Tensor . flout LinearMap
  contractMapTensor = flout LinearMap . flout Tensor
  applyDualVector = scale
  applyLinear = LinearFunction $ \(LinearMap w) -> scaleV w
  applyTensorFunctional = bilinearFunction $ \(LinearMap du) (Tensor u) -> du<.>^u
  applyTensorLinMap = bilinearFunction $ \fℝuw (Tensor u)
                        -> let LinearMap fuw = curryLinearMap $ fℝuw
                           in (applyLinear-+$>fuw) -+$> u
  composeLinear = bilinearFunction $ \f (LinearMap g)
                     -> LinearMap $ (applyLinear-+$>f)-+$>g

#define FreeLinearSpace(V, LV, tp, tenspl, tenid, dspan, contraction, contraaction)  \
instance Num s => Semimanifold (V s) where {  \
  type Needle (V s) = V s;                      \
  toInterior = pure; fromInterior = id;           \
  (.+~^) = (^+^);                                     \
  translateP = Tagged (^+^) };                      \
instance Num s => PseudoAffine (V s) where {         \
  v.-~.w = pure (v^-^w); (.-~!) = (^-^) };              \
instance ∀ s . Num' s => TensorSpace (V s) where {                     \
  type TensorProduct (V s) w = V w;                               \
  scalarSpaceWitness = case closedScalarWitness :: ClosedScalarWitness s of{ \
                         ClosedScalarWitness -> ScalarSpaceWitness};        \
  linearManifoldWitness = LinearManifoldWitness BoundarylessWitness;   \
  zeroTensor = Tensor $ pure zeroV;                                \
  addTensors (Tensor m) (Tensor n) = Tensor $ liftA2 (^+^) m n;     \
  subtractTensors (Tensor m) (Tensor n) = Tensor $ liftA2 (^-^) m n; \
  negateTensor = LinearFunction $ Tensor . fmap negateV . getTensorProduct;  \
  scaleTensor = bilinearFunction   \
          $ \μ -> Tensor . fmap (μ*^) . getTensorProduct; \
  toFlatTensor = case closedScalarWitness :: ClosedScalarWitness s of{ \
                         ClosedScalarWitness -> follow Tensor}; \
  fromFlatTensor = case closedScalarWitness :: ClosedScalarWitness s of{ \
                         ClosedScalarWitness -> flout Tensor}; \
  tensorProduct = bilinearFunction $ \w v -> Tensor $ fmap (*^v) w; \
  transposeTensor = LinearFunction (tp); \
  fmapTensor = bilinearFunction $       \
          \(LinearFunction f) -> pretendLike Tensor $ fmap f; \
  fzipTensorWith = bilinearFunction $ \
          \(LinearFunction f) (Tensor vw, Tensor vx) \
                  -> Tensor $ liftA2 (curry f) vw vx; \
  coerceFmapTensorProduct _ Coercion = Coercion };                  \
instance ∀ s . Num' s => LinearSpace (V s) where {                  \
  type DualVector (V s) = V s;                                 \
  dualSpaceWitness = case closedScalarWitness :: ClosedScalarWitness s of \
         {ClosedScalarWitness -> DualSpaceWitness};                    \
  linearId = LV Mat.identity;                                   \
  idTensor = Tensor Mat.identity; \
  tensorId = ti dualSpaceWitness where     \
   { ti :: ∀ w . (LinearSpace w, Scalar w ~ s) => DualSpaceWitness w -> (V s⊗w)+>(V s⊗w) \
   ; ti DualSpaceWitness = LinearMap $ \
          fmap (\f -> fmap (LinearFunction $ Tensor . f)-+$>asTensor $ id) \
               (tenid :: V (w -> V w)) }; \
  coerceDoubleDual = Coercion; \
  fromLinearForm = case closedScalarWitness :: ClosedScalarWitness s of{ \
                         ClosedScalarWitness -> flout LinearMap}; \
  contractTensorMap = LinearFunction $ (contraction) . coerce . getLinearMap;      \
  contractMapTensor = LinearFunction $ (contraction) . coerce . getTensorProduct;      \
{-contractTensorWith = bilinearFunction $ \
            \(Tensor wv) dw -> fmap (arr $ applyDualVector $ dw) wv;  -}    \
  contractLinearMapAgainst = bilinearFunction $ getLinearMap >>> (contraaction); \
  applyDualVector = bilinearFunction Mat.dot;           \
  applyLinear = bilinearFunction $ \(LV m)                        \
                  -> foldl' (^+^) zeroV . liftA2 (^*) m;           \
  applyTensorFunctional = bilinearFunction $ \(LinearMap f) (Tensor t) \
             -> sum $ liftA2 (<.>^) f t; \
  applyTensorLinMap = bilinearFunction $ \(LinearMap f) (Tensor t) \
             -> foldl' (^+^) zeroV $ liftA2 (arr fromTensor >>> \
                         getLinearFunction . getLinearFunction applyLinear) f t; \
  composeLinear = bilinearFunction $   \
         \f (LinearMap g) -> LinearMap $ fmap ((applyLinear-+$>f)-+$>) g }
FreeLinearSpace( V0
               , LinearMap
               , \(Tensor V0) -> zeroV
               , \_ -> LinearMap V0
               , V0
               , LinearMap V0
               , \V0 -> zeroV
               , \V0 _ -> 0 )
FreeLinearSpace( V1
               , LinearMap
               , \(Tensor (V1 w₀)) -> w₀⊗V1 1
               , \w -> LinearMap $ V1 (Tensor $ V1 w)
               , V1 V1
               , LinearMap . V1 . blockVectSpan $ V1 1
               , \(V1 (V1 w)) -> w
               , \(V1 x) f -> (f$x)^._x )
FreeLinearSpace( V2
               , LinearMap
               , \(Tensor (V2 w₀ w₁)) -> w₀⊗V2 1 0
                                     ^+^ w₁⊗V2 0 1
               , \w -> LinearMap $ V2 (Tensor $ V2 w zeroV)
                                      (Tensor $ V2 zeroV w)
               , V2 (`V2`zeroV) (V2 zeroV)
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
               , \w -> LinearMap $ V3 (Tensor $ V3 w zeroV zeroV)
                                      (Tensor $ V3 zeroV w zeroV)
                                      (Tensor $ V3 zeroV zeroV w)
               , V3 (\w -> V3 w zeroV zeroV)
                    (\w -> V3 zeroV w zeroV)
                    (\w -> V3 zeroV zeroV w)
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
               , V4 (\w -> V4 w zeroV zeroV zeroV)
                    (\w -> V4 zeroV w zeroV zeroV)
                    (\w -> V4 zeroV zeroV w zeroV)
                    (\w -> V4 zeroV zeroV zeroV w)
               , LinearMap $ V4 (blockVectSpan $ V4 1 0 0 0)
                                (blockVectSpan $ V4 0 1 0 0)
                                (blockVectSpan $ V4 0 0 1 0)
                                (blockVectSpan $ V4 0 0 0 1)
               , \(V4 (V4 w₀ _ _ _)
                      (V4 _ w₁ _ _)
                      (V4 _ _ w₂ _)
                      (V4 _ _ _ w₃)) -> w₀^+^w₁^+^w₂^+^w₃
               , \(V4 x y z w) f -> (f$x)^._x + (f$y)^._y + (f$z)^._z + (f$w)^._w )



instance (Num' n, TensorProduct (DualVector n) n ~ n) => Num (LinearMap n n n) where
  LinearMap n + LinearMap m = LinearMap $ n + m
  LinearMap n - LinearMap m = LinearMap $ n - m
  LinearMap n * LinearMap m = LinearMap $ n * m
  abs (LinearMap n) = LinearMap $ abs n
  signum (LinearMap n) = LinearMap $ signum n
  fromInteger = LinearMap . fromInteger
   
instance (Fractional' n, TensorProduct (DualVector n) n ~ n)
                           => Fractional (LinearMap n n n) where
  LinearMap n / LinearMap m = LinearMap $ n / m
  recip (LinearMap n) = LinearMap $ recip n
  fromRational = LinearMap . fromRational






