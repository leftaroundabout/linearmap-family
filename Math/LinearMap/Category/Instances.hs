-- |
-- Module      : Math.LinearMap.Category.Instances
-- Copyright   : (c) Justus Sagemüller 2016-2019
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
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
{-# LANGUAGE StandaloneDeriving         #-}
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
import Data.VectorSpace.Free.FiniteSupportedSequence
import Data.VectorSpace.Free.Sequence as Seq
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import qualified Linear.Metric as Mat
import Linear ( V0(V0), V1(V1), V2(V2), V3(V3), V4(V4)
              , _x, _y, _z, _w )
import Control.Lens ((^.))

import qualified Data.Vector as Arr
import qualified Data.Vector.Unboxed as UArr

import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional

import qualified Test.QuickCheck as QC

import qualified GHC.Exts as GHC
import qualified GHC.Generics as GHC

infixr 7 <.>^
(<.>^) :: LinearSpace v => DualVector v -> v -> Scalar v
f<.>^v = (applyDualVector-+$>f)-+$>v

type ℝ = Double

autoLinearManifoldWitness :: (Semimanifold v, AffineSpace v, v ~ Needle v, v ~ Diff v
#if !MIN_VERSION_manifolds_core(0,6,0)
                             , v ~ Interior v
#endif
                             )
                                 => LinearManifoldWitness v
autoLinearManifoldWitness = LinearManifoldWitness
#if !MIN_VERSION_manifolds_core(0,6,0)
                             BoundarylessWitness
#endif

#define LinearScalarSpace(S) \
instance Num' (S) where {closedScalarWitness = ClosedScalarWitness}; \
instance TensorSpace (S) where { \
  type TensorProduct (S) w = w; \
  scalarSpaceWitness = ScalarSpaceWitness; \
  linearManifoldWitness = autoLinearManifoldWitness; \
  zeroTensor = Tensor zeroV; \
  scaleTensor = bilinearFunction $ \μ (Tensor t) -> Tensor $ μ*^t; \
  addTensors (Tensor v) (Tensor w) = Tensor $ v ^+^ w; \
  subtractTensors (Tensor v) (Tensor w) = Tensor $ v ^-^ w; \
  negateTensor = pretendLike Tensor lNegateV; \
  toFlatTensor = follow Tensor; \
  fromFlatTensor = flout Tensor; \
  tensorProduct = LinearFunction $ \μ -> follow Tensor . scaleWith μ; \
  transposeTensor = toFlatTensor . flout Tensor; \
  fmapTensor = LinearFunction $ pretendLike Tensor; \
  fzipTensorWith = LinearFunction \
                   $ \f -> follow Tensor <<< f <<< flout Tensor *** flout Tensor; \
  coerceFmapTensorProduct _ Coercion = Coercion; \
  wellDefinedTensor (Tensor w) = Tensor <$> wellDefinedVector w }; \
instance LinearSpace (S) where { \
  type DualVector (S) = (S); \
  dualSpaceWitness = DualSpaceWitness; \
  linearId = LinearMap 1; \
  tensorId = uncurryLinearMap $ LinearMap $ fmap (follow Tensor) -+$> id; \
  idTensor = Tensor 1; \
  fromLinearForm = flout LinearMap; \
  coerceDoubleDual = Coercion; \
  contractTensorMap = flout Tensor . flout LinearMap; \
  contractMapTensor = flout LinearMap . flout Tensor; \
  applyDualVector = scale; \
  applyLinear = LinearFunction $ \(LinearMap w) -> scaleV w; \
  applyTensorFunctional = bilinearFunction $ \(LinearMap du) (Tensor u) -> du<.>^u; \
  applyTensorLinMap = bilinearFunction $ \fℝuw (Tensor u) \
                        -> let LinearMap fuw = curryLinearMap $ fℝuw \
                           in (applyLinear-+$>fuw) -+$> u; \
  composeLinear = bilinearFunction $ \f (LinearMap g) \
                     -> LinearMap $ (applyLinear-+$>f)-+$>g }

LinearScalarSpace(ℝ)
LinearScalarSpace(Float)
LinearScalarSpace(Rational)


#if MIN_VERSION_manifolds_core(0,6,0)
#define FreeLinSpaceInteriorDecls
#else
#define FreeLinSpaceInteriorDecls \
  toInterior = pure; fromInterior = id; translateP = Tagged (^+^);
#endif

#define FreeLinearSpace(V, LV, tp, tenspl, tenid, dspan, contraction, contraaction)  \
instance Num s => Semimanifold (V s) where {  \
  type Needle (V s) = V s;                      \
  FreeLinSpaceInteriorDecls                      \
  (.+~^) = (^+^) };                               \
instance Num s => PseudoAffine (V s) where {         \
  v.-~.w = pure (v^-^w); (.-~!) = (^-^) };              \
instance ∀ s . (Num' s, Eq s) => TensorSpace (V s) where {                     \
  type TensorProduct (V s) w = V w;                               \
  scalarSpaceWitness = case closedScalarWitness :: ClosedScalarWitness s of{ \
                         ClosedScalarWitness -> ScalarSpaceWitness};        \
  linearManifoldWitness = autoLinearManifoldWitness;   \
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
  coerceFmapTensorProduct _ Coercion = Coercion; \
  wellDefinedTensor = getTensorProduct >>> Hask.traverse wellDefinedVector \
                       >>> fmap Tensor };                  \
instance ∀ s . (Num' s, Eq s) => LinearSpace (V s) where {                  \
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




instance (Num' n, UArr.Unbox n) => Semimanifold (FinSuppSeq n) where
  type Needle (FinSuppSeq n) = FinSuppSeq n
  (.+~^) = (.+^)
#if !MIN_VERSION_manifolds_core(0,6,0)
  translateP = Tagged (.+^); toInterior = pure; fromInterior = id
#endif

instance (Num' n, UArr.Unbox n) => PseudoAffine (FinSuppSeq n) where
  v.-~.w = Just $ v.-.w; (.-~!) = (.-.)

instance (Num' n, UArr.Unbox n) => TensorSpace (FinSuppSeq n) where
  type TensorProduct (FinSuppSeq n) v = [v]
  wellDefinedVector (FinSuppSeq v) = FinSuppSeq <$> UArr.mapM wellDefinedVector v
  scalarSpaceWitness = case closedScalarWitness :: ClosedScalarWitness n of
        ClosedScalarWitness -> ScalarSpaceWitness
  linearManifoldWitness = autoLinearManifoldWitness
  zeroTensor = Tensor []
  toFlatTensor = LinearFunction $ Tensor . UArr.toList . getFiniteSeq
  fromFlatTensor = LinearFunction $ FinSuppSeq . UArr.fromList . getTensorProduct
  addTensors (Tensor s) (Tensor t) = Tensor $ Mat.liftU2 (^+^) s t
  subtractTensors (Tensor s) (Tensor t) = Tensor $ Mat.liftU2 (^-^) s t
  scaleTensor = bilinearFunction $ \μ (Tensor t) -> Tensor $ (μ*^)<$>t
  negateTensor = LinearFunction $ \(Tensor t) -> Tensor $ negateV<$>t
  tensorProduct = bilinearFunction
                    $ \(FinSuppSeq v) w -> Tensor $ (*^w)<$>UArr.toList v
  transposeTensor = LinearFunction $ \(Tensor a)
    -> let n = length a
       in foldl' (^+^) zeroV
        $ zipWith ( \i w -> getLinearFunction tensorProduct w $ basisValue i )
             [0..] a
  fmapTensor = bilinearFunction $ \f (Tensor a) -> Tensor $ map (f$) a
  fzipTensorWith = bilinearFunction $ \f (Tensor a, Tensor b)
                     -> Tensor $ zipWith (curry $ arr f) a b
  coerceFmapTensorProduct _ Coercion = Coercion
  wellDefinedTensor (Tensor a) = Tensor <$> Hask.traverse wellDefinedVector a
  

instance (Num' n, UArr.Unbox n) => Semimanifold (Sequence n) where
  type Needle (Sequence n) = Sequence n
  (.+~^) = (.+^)
#if !MIN_VERSION_manifolds_core(0,6,0)
  translateP = Tagged (.+^); toInterior = pure; fromInterior = id
#endif

instance (Num' n, UArr.Unbox n) => PseudoAffine (Sequence n) where
  v.-~.w = Just $ v.-.w; (.-~!) = (.-.)

instance (Num' n, UArr.Unbox n) => TensorSpace (Sequence n) where
  type TensorProduct (Sequence n) v = [v]
  wellDefinedVector (SoloChunk n c) = SoloChunk n <$> UArr.mapM wellDefinedVector c
  wellDefinedVector (Sequence h r) = Sequence <$> UArr.mapM wellDefinedVector h
                                              <*> wellDefinedVector r
  wellDefinedTensor (Tensor a) = Tensor <$> Hask.traverse wellDefinedVector a
  scalarSpaceWitness = case closedScalarWitness :: ClosedScalarWitness n of
        ClosedScalarWitness -> ScalarSpaceWitness
  linearManifoldWitness = autoLinearManifoldWitness
  zeroTensor = Tensor []
  toFlatTensor = LinearFunction $ Tensor . GHC.toList
  fromFlatTensor = LinearFunction $ GHC.fromList . getTensorProduct
  addTensors (Tensor s) (Tensor t) = Tensor $ Mat.liftU2 (^+^) s t
  subtractTensors (Tensor s) (Tensor t) = Tensor $ Mat.liftU2 (^-^) s t
  scaleTensor = bilinearFunction $ \μ (Tensor t) -> Tensor $ (μ*^)<$>t
  negateTensor = LinearFunction $ \(Tensor t) -> Tensor $ negateV<$>t
  tensorProduct = bilinearFunction
                    $ \v w -> Tensor $ (*^w)<$>GHC.toList v
  transposeTensor = LinearFunction $ \(Tensor a)
    -> let n = length a
       in foldl' (^+^) zeroV
        $ zipWith (\i w -> (getLinearFunction tensorProduct w) $ basisValue i)
             [0..] a
  fmapTensor = bilinearFunction $ \f (Tensor a) -> Tensor $ map (f$) a
  fzipTensorWith = bilinearFunction $ \f (Tensor a, Tensor b)
                     -> Tensor $ zipWith (curry $ arr f) a b
  coerceFmapTensorProduct _ Coercion = Coercion

instance (Num' n, UArr.Unbox n) => LinearSpace (Sequence n) where
  type DualVector (Sequence n) = FinSuppSeq n
  dualSpaceWitness = case closedScalarWitness :: ClosedScalarWitness n of
            ClosedScalarWitness -> DualSpaceWitness
  linearId = LinearMap [basisValue i | i<-[0..]]
  tensorId = LinearMap [asTensor $ fmap (LinearFunction $
                           \w -> Tensor $ replicate (i-1) zeroV ++ [w]) $ id | i<-[0..]]
  applyDualVector = bilinearFunction $ adv Seq.minimumChunkSize
   where adv _ (FinSuppSeq v) (Seq.SoloChunk o q)
               = UArr.sum $ UArr.zipWith (*) (UArr.drop o v) q
         adv chunkSize (FinSuppSeq v) (Sequence c r)
          | UArr.length v > chunkSize
                       = UArr.sum (UArr.zipWith (*) v c)
                            + adv (chunkSize*2) (FinSuppSeq $ UArr.drop chunkSize v) r
          | otherwise  = UArr.sum $ UArr.zipWith (*) v c
  applyLinear = bilinearFunction $ apl Seq.minimumChunkSize
   where apl _ (LinearMap m) (Seq.SoloChunk o q)
               = sumV $ zipWith (*^) (UArr.toList q) (drop o m)
         apl chunkSize (LinearMap m) (Sequence c r)
          | null mr    = sumV $ zipWith (*^) (UArr.toList c) mc
          | otherwise  = foldl' (^+^) (apl (chunkSize*2) (LinearMap mr) r)
                                      (zipWith (*^) (UArr.toList c) mc)
          where (mc, mr) = splitAt chunkSize m
  applyTensorFunctional = bilinearFunction
       $ \(LinearMap m) (Tensor t) -> sum $ zipWith (<.>^) m t
  applyTensorLinMap = bilinearFunction $ arr curryLinearMap >>>
         \(LinearMap m) (Tensor t)
             -> sumV $ zipWith (getLinearFunction . getLinearFunction applyLinear) m t
instance (Num' n, UArr.Unbox n) => LinearSpace (FinSuppSeq n) where
  type DualVector (FinSuppSeq n) = Sequence n
  dualSpaceWitness = case closedScalarWitness :: ClosedScalarWitness n of
            ClosedScalarWitness -> DualSpaceWitness
  linearId = LinearMap [basisValue i | i<-[0..]]
  tensorId = LinearMap [asTensor $ fmap (LinearFunction $
                           \w -> Tensor $ replicate (i-1) zeroV ++ [w]) $ id | i<-[0..]]
  applyDualVector = bilinearFunction $ adv Seq.minimumChunkSize
   where adv _ (Seq.SoloChunk o q) (FinSuppSeq v)
               = UArr.sum $ UArr.zipWith (*) q (UArr.drop o v)
         adv chunkSize (Sequence c r) (FinSuppSeq v)
          | UArr.length v > chunkSize
                       = UArr.sum (UArr.zipWith (*) c v)
                            + adv (chunkSize*2) r (FinSuppSeq $ UArr.drop chunkSize v)
          | otherwise  = UArr.sum $ UArr.zipWith (*) c v
  applyLinear = bilinearFunction $ \(LinearMap m) (FinSuppSeq v)
                   -> foldl' (^+^) zeroV $ zipWith (*^) (UArr.toList v) m
  applyTensorFunctional = bilinearFunction
       $ \(LinearMap m) (Tensor t) -> sum $ zipWith (<.>^) m t
  applyTensorLinMap = bilinearFunction $ arr curryLinearMap >>>
         \(LinearMap m) (Tensor t)
             -> sumV $ zipWith (getLinearFunction . getLinearFunction applyLinear) m t
  


instance GHC.IsList (Tensor s (Sequence s) v) where
  type Item (Tensor s (Sequence s) v) = v
  fromList = Tensor
  toList = getTensorProduct

instance GHC.IsList (Tensor s (FinSuppSeq s) v) where
  type Item (Tensor s (FinSuppSeq s) v) = v
  fromList = Tensor
  toList = getTensorProduct



newtype SymmetricTensor s v
           = SymTensor { getSymmetricTensor :: Tensor s v v }
deriving instance (Show (Tensor s v v)) => Show (SymmetricTensor s v)

instance (TensorSpace v, Scalar v ~ s) => AffineSpace (SymmetricTensor s v) where
  type Diff (SymmetricTensor s v) = SymmetricTensor s v
  (.+^) = (^+^)
  (.-.) = (^-^)
instance (TensorSpace v, Scalar v ~ s) => AdditiveGroup (SymmetricTensor s v) where
  SymTensor s ^+^ SymTensor t = SymTensor $ s ^+^ t
  zeroV = SymTensor zeroV
  negateV (SymTensor t) = SymTensor $ negateV t

instance (TensorSpace v, Scalar v ~ s)
             => VectorSpace (SymmetricTensor s v) where
  type Scalar (SymmetricTensor s v) = s
  μ *^ SymTensor f = SymTensor $ μ*^f

instance (TensorSpace v, Scalar v ~ s) => Semimanifold (SymmetricTensor s v) where
  type Needle (SymmetricTensor s v) = SymmetricTensor s v
  (.+~^) = (^+^)
#if !MIN_VERSION_manifolds_core(0,6,0)
  fromInterior = id
  toInterior = pure
  translateP = Tagged (^+^)
#endif
instance (TensorSpace v, Scalar v ~ s) => PseudoAffine (SymmetricTensor s v) where
  (.-~!) = (^-^)
instance (Num' s, TensorSpace v, Scalar v ~ s) => TensorSpace (SymmetricTensor s v) where
  type TensorProduct (SymmetricTensor s v) x = Tensor s v (Tensor s v x)
  wellDefinedVector (SymTensor t) = SymTensor <$> wellDefinedVector t
  scalarSpaceWitness = case closedScalarWitness :: ClosedScalarWitness s of
        ClosedScalarWitness -> ScalarSpaceWitness
  linearManifoldWitness = autoLinearManifoldWitness
  zeroTensor = Tensor zeroV
  toFlatTensor = case closedScalarWitness :: ClosedScalarWitness s of
        ClosedScalarWitness -> LinearFunction $ \(SymTensor t)
                                 -> Tensor $ fmap toFlatTensor $ t
  fromFlatTensor = case closedScalarWitness :: ClosedScalarWitness s of
        ClosedScalarWitness -> LinearFunction $ \(Tensor t)
                     -> SymTensor $ fmap fromFlatTensor $ t
  addTensors (Tensor f) (Tensor g) = Tensor $ f^+^g
  subtractTensors (Tensor f) (Tensor g) = Tensor $ f^-^g
  negateTensor = LinearFunction $ \(Tensor f) -> Tensor $ negateV f
  scaleTensor = bilinearFunction $ \μ (Tensor f) -> Tensor $ μ *^ f
  tensorProduct = bilinearFunction $ \(SymTensor t) g
                    -> Tensor $ fmap (LinearFunction (⊗g)) $ t
  transposeTensor = LinearFunction $ \(Tensor f) -> getLinearFunction (
                            arr (fmap Coercion) . transposeTensor . arr lassocTensor) f
  fmapTensor = bilinearFunction $ \f (Tensor t) -> Tensor $ fmap (fmap f) $ t
  fzipTensorWith = bilinearFunction $ \f (Tensor s, Tensor t)
                 -> Tensor $ fzipWith (fzipWith f) $ (s,t)
  coerceFmapTensorProduct _ crc = fmap (fmap crc)
  wellDefinedTensor (Tensor t) = Tensor <$> wellDefinedVector t

instance (Num' s, LinearSpace v, Scalar v ~ s) => LinearSpace (SymmetricTensor s v) where
  type DualVector (SymmetricTensor s v) = SymmetricTensor s (DualVector v)
  dualSpaceWitness = case ( closedScalarWitness :: ClosedScalarWitness s
                          , dualSpaceWitness :: DualSpaceWitness v ) of 
          (ClosedScalarWitness, DualSpaceWitness) -> DualSpaceWitness
  linearId = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> LinearMap $ rassocTensor . asTensor
                          . fmap (follow SymTensor . asTensor) $ id
  tensorId = LinearMap $ asTensor . fmap asTensor . curryLinearMap
                           . fmap asTensor
                           . curryLinearMap
                           . fmap (follow $ \t -> Tensor $ rassocTensor $ t)
                           $ id
  applyLinear = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> bilinearFunction $ \(LinearMap f) (SymTensor t)
                   -> (getLinearFunction applyLinear
                         $ fromTensor . deferLinearMap . asLinearMap $ f) $ t
  applyDualVector = bilinearFunction $ \(SymTensor f) (SymTensor v)
                      -> getLinearFunction
                           (getLinearFunction applyDualVector $ fromTensor $ f) v
  applyTensorFunctional = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> bilinearFunction $ \(LinearMap f) (Tensor t)
                   -> getLinearFunction
                        (getLinearFunction applyTensorFunctional
                             $ fromTensor . fmap fromTensor $ f) t
  applyTensorLinMap = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> bilinearFunction $ \(LinearMap (Tensor f)) (Tensor t)
                   -> getLinearFunction (getLinearFunction applyTensorLinMap
                             $ uncurryLinearMap
                                . fmap (uncurryLinearMap . fromTensor . fmap fromTensor)
                                       $ LinearMap f) t  




squareV :: (Num' s, s ~ Scalar v)
          => TensorSpace v => v -> SymmetricTensor s v
squareV v = SymTensor $ v⊗v

squareVs :: (Num' s, s ~ Scalar v)
          => TensorSpace v => [v] -> SymmetricTensor s v
squareVs vs = SymTensor $ tensorProducts [(v,v) | v<-vs]


type v⊗〃+>w = LinearMap (Scalar v) (SymmetricTensor (Scalar v) v) w

currySymBilin :: LinearSpace v => (v⊗〃+>w) -+> (v+>(v+>w))
currySymBilin = LinearFunction . arr $ fmap fromTensor . fromTensor . flout LinearMap





newtype LinearApplicativeSpace f y
    = LinearApplicativeSpace { getLinearApplicativeSpace :: f y }

instance ( GHC.Generic1 f, TensorSpace y
         , TensorSpace (f y), Scalar (f y) ~ Scalar y
         , Monoidal f (LinearFunction (Scalar y)) (LinearFunction (Scalar y)) )
     => AffineSpace (LinearApplicativeSpace f y) where
  type Diff (LinearApplicativeSpace f y) = LinearApplicativeSpace f y
  (.+^) = (^+^)
  (.-.) = (^-^)

instance ∀ f y . ( GHC.Generic1 f, TensorSpace y
                 , TensorSpace (f y), Scalar (f y) ~ Scalar y
                 , Monoidal f (LinearFunction (Scalar y)) (LinearFunction (Scalar y)) )
     => AdditiveGroup (LinearApplicativeSpace f y) where
  zeroV = LinearApplicativeSpace $ getLinearFunction
             ( fmap zeroV
              . (pureUnit :: LinearFunction (Scalar y) (ZeroDim (Scalar y))
                                                       (f (ZeroDim (Scalar y)))) ) zeroV
  LinearApplicativeSpace a^+^LinearApplicativeSpace b
    = LinearApplicativeSpace
     $ getLinearFunction
           (fzipWith (LinearFunction $ uncurry (^+^)))
           (a,b)
  LinearApplicativeSpace a^-^LinearApplicativeSpace b
    = LinearApplicativeSpace
     $ getLinearFunction
           (fzipWith (LinearFunction $ uncurry (^-^)))
           (a,b)
  negateV (LinearApplicativeSpace a) = LinearApplicativeSpace
       $ getLinearFunction (fmap $ LinearFunction negateV) a

instance ( GHC.Generic1 f, TensorSpace y
         , TensorSpace (f y), Scalar (f y) ~ Scalar y
         , Monoidal f (LinearFunction (Scalar y)) (LinearFunction (Scalar y)) )
     => VectorSpace (LinearApplicativeSpace f y) where
  type Scalar (LinearApplicativeSpace f y) = Scalar y
  (*^) = undefined

instance ( GHC.Generic1 f, TensorSpace y
         , TensorSpace (f y), Scalar (f y) ~ Scalar y
         , Monoidal f (LinearFunction (Scalar y)) (LinearFunction (Scalar y)) )
     => Semimanifold (LinearApplicativeSpace f y) where
  type Needle (LinearApplicativeSpace f y) = LinearApplicativeSpace f y
#if !MIN_VERSION_manifolds_core(0,6,0)
  type Interior (LinearApplicativeSpace f y) = LinearApplicativeSpace f y
  toInterior = Just; fromInterior = id
  translateP = Tagged (^+^)
#endif
  (.+~^) = (^+^)

instance ( GHC.Generic1 f, TensorSpace y
         , TensorSpace (f y), Scalar (f y) ~ Scalar y
         , Monoidal f (LinearFunction (Scalar y)) (LinearFunction (Scalar y)) )
     => PseudoAffine (LinearApplicativeSpace f y) where
  (.-~!) = (.-.)



instance (InnerSpace v, Scalar v ~ ℝ, TensorSpace v)
              => InnerSpace (Tensor ℝ ℝ v) where
  Tensor t <.> Tensor u = t <.> u

instance (Show v) => Show (Tensor ℝ ℝ v) where
  showsPrec p (Tensor t) = showParen (p>9) $ ("Tensor "++) . showsPrec 10 t

instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (Tensor ℝ ℝ v) where
  arbitrary = Tensor <$> QC.arbitrary
  shrink (Tensor t) = Tensor <$> QC.shrink t

instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (LinearMap ℝ ℝ v) where
  arbitrary = LinearMap <$> QC.arbitrary
  shrink (LinearMap t) = LinearMap <$> QC.shrink t

