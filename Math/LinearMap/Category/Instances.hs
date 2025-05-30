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
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE TypeApplications           #-}

module Math.LinearMap.Category.Instances where

import Math.VectorSpace.DimensionAware
import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances.THHelpers

import Data.VectorSpace
import Data.Basis

#if MIN_VERSION_manifolds_core(0,6,0)
import Math.Manifold.Core.Types (EmptyMfd)
#endif
import Math.Manifold.Core.Types (ℝ)
import Math.Manifold.Core.PseudoAffine

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion
import Data.Tagged
import Data.Proxy

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
import Control.Monad.ST (ST)

import qualified Data.Vector as Arr
import qualified Data.Vector.Unboxed as UArr
import qualified Data.Vector.Generic as GArr

import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional
import qualified Math.VectorSpace.DimensionAware.Theorems.MaybeNat as Maybe

import qualified Test.QuickCheck as QC

import GHC.TypeNats (natVal)
import qualified GHC.Exts as GHC
import qualified GHC.Generics as GHC

import Data.Singletons (SingI, sing, Sing)
#if MIN_VERSION_singletons(3,0,0)
import GHC.TypeLits.Singletons (withKnownNat)
#else
import Data.Singletons.TypeLits (withKnownNat)
#endif


#if MIN_VERSION_manifolds_core(0,6,0)
instance LinearSpace v => Semimanifold (EmptyMfd v) where
  type Needle (EmptyMfd v) = v
  p .+~^ _ = case p of {}
  p .-~^ _ = case p of {}
  semimanifoldWitness = case linearManifoldWitness @v of
    LinearManifoldWitness -> SemimanifoldWitness
instance LinearSpace v => PseudoAffine (EmptyMfd v) where
  p .-~. _ = case p of {}
  p .-~! _ = case p of {}
#endif


infixr 7 <.>^
(<.>^) :: LinearSpace v => DualVector v -> v -> Scalar v
f<.>^v = (applyDualVector-+$>f)-+$>v


mkLinearScalarSpace ''ℝ
mkLinearScalarSpace ''Float
mkLinearScalarSpace ''Rational


mkFreeLinearSpace ''V0 'V0 0
mkFreeLinearSpace ''V1 'V1 1
mkFreeLinearSpace ''V2 'V2 2
mkFreeLinearSpace ''V3 'V3 3
mkFreeLinearSpace ''V4 'V4 4



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

instance (Num' n, UArr.Unbox n) => DimensionAware (FinSuppSeq n) where
  type StaticDimension (FinSuppSeq n) = 'Nothing
  dimensionalityWitness = IsFlexibleDimensional
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
  tensorUnsafeFromArrayWithOffset
      = notStaticDimensionalContradiction @(FinSuppSeq n)
  tensorUnsafeWriteArrayWithOffset
      = notStaticDimensionalContradiction @(FinSuppSeq n)
  coerceFmapTensorProduct _ VSCCoercion = Coercion
  wellDefinedTensor (Tensor a) = Tensor <$> Hask.traverse wellDefinedVector a
  

instance (Num' n, UArr.Unbox n) => Semimanifold (Sequence n) where
  type Needle (Sequence n) = Sequence n
  (.+~^) = (.+^)
#if !MIN_VERSION_manifolds_core(0,6,0)
  translateP = Tagged (.+^); toInterior = pure; fromInterior = id
#endif

instance (Num' n, UArr.Unbox n) => PseudoAffine (Sequence n) where
  v.-~.w = Just $ v.-.w; (.-~!) = (.-.)

instance (Num' n, UArr.Unbox n) => DimensionAware (Sequence n) where
  type StaticDimension (Sequence n) = 'Nothing
  dimensionalityWitness = IsFlexibleDimensional
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
  tensorUnsafeFromArrayWithOffset
      = notStaticDimensionalContradiction @(Sequence n)
  tensorUnsafeWriteArrayWithOffset
      = notStaticDimensionalContradiction @(Sequence n)
  coerceFmapTensorProduct _ VSCCoercion = Coercion

instance ∀ n . (Num' n, UArr.Unbox n) => LinearSpace (Sequence n) where
  type DualVector (Sequence n) = FinSuppSeq n
  dualSpaceWitness = case closedScalarWitness :: ClosedScalarWitness n of
            ClosedScalarWitness -> DualSpaceWitness
  linearId = LinearMap [basisValue i | i<-[0..]]
  tensorId = LinearMap [asTensor -+$=> fmap (LinearFunction $
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
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError
  coerceDoubleDual = case scalarSpaceWitness @n of
     ScalarSpaceWitness -> VSCCoercion
instance ∀ n . (Num' n, UArr.Unbox n) => LinearSpace (FinSuppSeq n) where
  type DualVector (FinSuppSeq n) = Sequence n
  dualSpaceWitness = case closedScalarWitness :: ClosedScalarWitness n of
            ClosedScalarWitness -> DualSpaceWitness
  linearId = LinearMap [basisValue i | i<-[0..]]
  tensorId = LinearMap [asTensor -+$=> fmap (LinearFunction $
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
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError
  coerceDoubleDual = case scalarSpaceWitness @n of
     ScalarSpaceWitness -> VSCCoercion
  


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
  p.-~.q = pure (p^-^q)
instance ∀ s v . (Num' s, TensorSpace v, Scalar v ~ s)
            => DimensionAware (SymmetricTensor s v) where
  type StaticDimension (SymmetricTensor s v) 
          = Maybe.FmapTriangularNum (StaticDimension v)
  dimensionalityWitness = case dimensionalityWitness @v of
     IsFlexibleDimensional -> IsFlexibleDimensional
     IsStaticDimensional
        -> withKnownNat (Maybe.triangularNumSing (dimensionalitySing @v))
              IsStaticDimensional
instance ∀ s v n m . ( Num' s, n`Dimensional`v, TensorSpace v, Scalar v ~ s
                     , m ~ Maybe.TriangularNum n )
                => m`Dimensional`(SymmetricTensor s v) where
  knownDimensionalitySing = Maybe.triangularNumSing $ dimensionalitySing @v
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
                            undefined -- arr (fmap VSCCoercion)
                            . transposeTensor . arr lassocTensor) f
  fmapTensor = bilinearFunction $ \f (Tensor t) -> Tensor $ fmap (fmap f) $ t
  fzipTensorWith = bilinearFunction $ \f (Tensor s, Tensor t)
                 -> Tensor $ fzipWith (fzipWith f) $ (s,t)
  coerceFmapTensorProduct _ crc = undefined -- case fmap (fmap crc) :: VSCCoercion of
      -- VSCCoercion -> Coercion
  wellDefinedTensor (Tensor t) = Tensor <$> wellDefinedVector t

instance ∀ s v . (Num' s, LinearSpace v, Scalar v ~ s)
                   => LinearSpace (SymmetricTensor s v) where
  type DualVector (SymmetricTensor s v) = SymmetricTensor s (DualVector v)
  dualSpaceWitness = case ( closedScalarWitness :: ClosedScalarWitness s
                          , dualSpaceWitness :: DualSpaceWitness v ) of 
          (ClosedScalarWitness, DualSpaceWitness) -> DualSpaceWitness
  linearId = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> LinearMap undefined
                         -- LinearMap $ rassocTensor . asTensor
                         -- . fmap (unsafeFollowVSC SymTensor . asTensor) $ id
  tensorId = LinearMap undefined
                   -- LinearMap $ asTensor . fmap asTensor . curryLinearMap
                   --  . fmap asTensor
                   --  . curryLinearMap
                   --  . fmap (unsafeFollowVSC $ \t -> Tensor $ rassocTensor $ t)
                   --  $ id
  applyLinear = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> bilinearFunction $ \(LinearMap f) (SymTensor t)
                   -> (getLinearFunction applyLinear
                         $ fromTensor . deferLinearMap . asLinearMap $ f) $ t
  applyDualVector = bilinearFunction $ \(SymTensor f) (SymTensor v)
                      -> getLinearFunction
                           (getLinearFunction applyDualVector $ fromTensor -+$=> f) v
  applyTensorFunctional :: ∀ u . (LinearSpace u, Scalar u ~ s)
       => LinearFunction s
               (LinearMap s (SymmetricTensor s v) (DualVector u))
               (LinearFunction s (Tensor s (SymmetricTensor s v) u) s)
  applyTensorFunctional = case (dualSpaceWitness @v, dualSpaceWitness @u) of
    (DualSpaceWitness, DualSpaceWitness)
             -> bilinearFunction $ \(LinearMap f) (Tensor t)
                   -> getLinearFunction
                        (getLinearFunction applyTensorFunctional
                             $ fromTensor . fmap fromTensor -+$=> f) t
  applyTensorLinMap :: ∀ u w . ( LinearSpace u, Scalar u ~ s
                               , TensorSpace w, Scalar w ~ s )
       => LinearFunction s
               (LinearMap s (Tensor s (SymmetricTensor s v) u) w)
               (LinearFunction s (Tensor s (SymmetricTensor s v) u) w)
  applyTensorLinMap = case (dualSpaceWitness @v, dualSpaceWitness @u) of
    (DualSpaceWitness, DualSpaceWitness)
              -> bilinearFunction $ \(LinearMap (Tensor f)) (Tensor t)
                   -> getLinearFunction (getLinearFunction applyTensorLinMap
                             $ uncurryLinearMap
                                . fmap (uncurryLinearMap . fromTensor . fmap fromTensor)
                                       -+$=> LinearMap f) t  
  useTupleLinearSpaceComponents _ = usingNonTupleTypeAsTupleError
  coerceDoubleDual = case (dualSpaceWitness @v, scalarSpaceWitness @s) of
     (DualSpaceWitness, ScalarSpaceWitness) -> VSCCoercion




squareV :: (Num' s, s ~ Scalar v)
          => TensorSpace v => v -> SymmetricTensor s v
squareV v = SymTensor $ v⊗v

squareVs :: (Num' s, s ~ Scalar v)
          => TensorSpace v => [v] -> SymmetricTensor s v
squareVs vs = SymTensor $ tensorProducts [(v,v) | v<-vs]


type v⊗〃+>w = LinearMap (Scalar v) (SymmetricTensor (Scalar v) v) w

currySymBilin :: LinearSpace v => (v⊗〃+>w) -+> (v+>(v+>w))
currySymBilin = undefined -- LinearFunction . arr $ fmap fromTensor . fromTensor . VSCCoercion





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
  p.-~.q = pure (p.-.q)



instance (InnerSpace v, Scalar v ~ ℝ, TensorSpace v)
              => InnerSpace (Tensor ℝ ℝ v) where
  Tensor t <.> Tensor u = t <.> u
instance (InnerSpace v, TensorSpace v, Scalar v ~ ℝ)
   => InnerSpace (LinearMap ℝ ℝ v) where
  LinearMap f <.> LinearMap g = f<.>g

instance ( TensorSpace u, TensorSpace v, TensorSpace w
         , Num s, Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
         , InnerSpace (Tensor s u w), InnerSpace (Tensor s v w) )
              => InnerSpace (Tensor s (u,v) w) where
  Tensor (uw,vw) <.> Tensor (uw',vw') = uw<.>uw' + vw<.>vw'
instance ( LinearSpace u, LinearSpace v, TensorSpace w
         , Num s, Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
         , InnerSpace (LinearMap s u w), InnerSpace (LinearMap s v w) )
              => InnerSpace (LinearMap s (u,v) w) where
  (<.>) = case (dualSpaceWitness @u, dualSpaceWitness @v) of
    (DualSpaceWitness, DualSpaceWitness)
      -> \(LinearMap (uw,vw)) (LinearMap (uw',vw'))
            -> (asLinearMap$uw)<.>(asLinearMap$uw')
                 + (asLinearMap$vw)<.>(asLinearMap$vw')

instance ( TensorSpace u, TensorSpace v, TensorSpace w
         , AdditiveGroup s, Num s
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
         , InnerSpace (Tensor s u (Tensor s v w)) )
              => InnerSpace (Tensor s (Tensor s u v) w) where
  s <.> t = (rassocTensor$s)<.>(rassocTensor$t)
instance ( LinearSpace u, TensorSpace v, TensorSpace w
         , AdditiveGroup s, Num s
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
         , InnerSpace (LinearMap s u (Tensor s v w)) )
              => InnerSpace (Tensor s (LinearMap s u v) w) where
  s <.> t = (hasteLinearMap$s)<.>(hasteLinearMap$t)
instance ( LinearSpace u, LinearSpace v, TensorSpace w
         , AdditiveGroup s, Num s
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
         , InnerSpace (LinearMap s u (LinearMap s v w)) )
              => InnerSpace (LinearMap s (Tensor s u v) w) where
  s <.> t = (curryLinearMap$s)<.>(curryLinearMap$t)
instance ( LinearSpace u, LinearSpace v, TensorSpace w
         , AdditiveGroup s, Num s
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
         , InnerSpace (Tensor s u (LinearMap s v w)) )
              => InnerSpace (LinearMap s (LinearMap s u v) w) where
  s <.> t = (coCurryLinearMap$s)<.>(coCurryLinearMap$t)

instance (Show v) => Show (Tensor ℝ ℝ v) where
  showsPrec p (Tensor t) = showParen (p>9) $ ("Tensor "++) . showsPrec 10 t

instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (Tensor ℝ ℝ v) where
  arbitrary = Tensor <$> QC.arbitrary
  shrink (Tensor t) = Tensor <$> QC.shrink t

instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (LinearMap ℝ ℝ v) where
  arbitrary = LinearMap <$> QC.arbitrary
  shrink (LinearMap t) = LinearMap <$> QC.shrink t

#define FreeArbitrarySpace(S) \
instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (Tensor ℝ (S ℝ) v) where { \
  arbitrary = Tensor <$> Hask.traverse (const QC.arbitrary) zeroV };  \
instance (QC.Arbitrary v, Scalar v ~ ℝ) => QC.Arbitrary (LinearMap ℝ (S ℝ) v) where { \
  arbitrary = LinearMap <$> Hask.traverse (const QC.arbitrary) zeroV }

FreeArbitrarySpace(V0)
FreeArbitrarySpace(V1)
FreeArbitrarySpace(V2)
FreeArbitrarySpace(V3)
FreeArbitrarySpace(V4)

instance ( QC.Arbitrary (Tensor s u w), QC.Arbitrary (Tensor s v w)
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s )
          => QC.Arbitrary (Tensor s (u,v) w) where
  arbitrary = Tensor <$> QC.arbitrary
  shrink (Tensor t) = Tensor <$> QC.shrink t

instance ( LinearSpace u, LinearSpace v, TensorSpace w
         , QC.Arbitrary (LinearMap s u w), QC.Arbitrary (LinearMap s v w)
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s )
          => QC.Arbitrary (LinearMap s (u,v) w) where
  arbitrary = case (dualSpaceWitness @u, dualSpaceWitness @v) of
   (DualSpaceWitness, DualSpaceWitness) -> LinearMap <$> do
     (,) <$> (arr fromLinearMap <$> QC.arbitrary)
         <*> (arr fromLinearMap <$> QC.arbitrary)
  shrink = case (dualSpaceWitness @u, dualSpaceWitness @v) of
   (DualSpaceWitness, DualSpaceWitness) -> \(LinearMap (x,y)) -> LinearMap <$> do
     (x',y') <- QC.shrink (asLinearMap $ x, asLinearMap $ y)
     return (fromLinearMap $ x', fromLinearMap $ y')

instance ( TensorSpace u, TensorSpace v, TensorSpace w
         , QC.Arbitrary (u⊗(v⊗w))
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s )
          => QC.Arbitrary (Tensor s (Tensor s u v) w) where
  arbitrary = arr lassocTensor <$> QC.arbitrary
  shrink (Tensor t) = arr lassocTensor <$> QC.shrink (Tensor t)

instance ( LinearSpace u, LinearSpace v, TensorSpace w
         , QC.Arbitrary (u+>(v+>w))
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s )
          => QC.Arbitrary (LinearMap s (Tensor s u v) w) where
  arbitrary = arr uncurryLinearMap <$> QC.arbitrary
  shrink f = arr uncurryLinearMap <$> QC.shrink (curryLinearMap $ f)

instance ( LinearSpace u, TensorSpace v, TensorSpace w
         , QC.Arbitrary (u+>(v⊗w))
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s )
          => QC.Arbitrary (Tensor s (LinearMap s u v) w) where
  arbitrary = arr deferLinearMap <$> QC.arbitrary
  shrink (Tensor t) = arr deferLinearMap <$> QC.shrink (LinearMap t)

instance ( LinearSpace u, LinearSpace v, TensorSpace w
         , QC.Arbitrary (u⊗(v+>w))
         , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s )
          => QC.Arbitrary (LinearMap s (LinearMap s u v) w) where
  arbitrary = arr coUncurryLinearMap <$> QC.arbitrary
  shrink f = arr coUncurryLinearMap <$> QC.shrink (coCurryLinearMap $ f)

