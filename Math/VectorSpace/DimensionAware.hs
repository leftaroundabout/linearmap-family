-- |
-- Module      : Math.VectorSpace.DimensionAware
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE CPP                    #-}

module Math.VectorSpace.DimensionAware where

import Data.VectorSpace

import Data.Singletons (SingI, sing, Sing)
#if MIN_VERSION_singletons(3,0,0)
import Prelude.Singletons (SNum(..))
import GHC.TypeLits.Singletons (withKnownNat)
#else
import Data.Singletons.Prelude.Num (SNum(..))
import Data.Singletons.TypeLits (withKnownNat)
#endif

import qualified Data.Vector.Generic as GArr
import qualified Data.Vector.Generic.Mutable as GMArr
import Control.Monad.ST (ST)

import Control.Monad

import GHC.TypeLits
import Data.Proxy (Proxy(..))

import Data.Ratio

import qualified Math.VectorSpace.DimensionAware.Theorems.MaybeNat as Maybe


-- | Low-level case distinction between spaces with a dimension that is both fixed
--   and low enough that it makes sense to treat it this way, and more general
--   spaces where this is not feasible.
--
--   Use this type only when defining instances of 'DimensionAware'. When making
--   decisions based on dimensionality, 'DimensionalityCases' is more convenient.
data DimensionalityWitness v where
  IsStaticDimensional :: (KnownNat n, n`Dimensional`v) => DimensionalityWitness v
  IsFlexibleDimensional :: StaticDimension v ~ 'Nothing => DimensionalityWitness v


-- | This class does not really pose any restrictions on a vector space type, but
--   allows it to express its dimension.
--   This is for optimisation purposes only, specifically to allow low-dimensional vectors
--   to be represented efficiently in unboxed arrays / matrices.
class VectorSpace v => DimensionAware v where
  -- | If this is `Nothing`,
  --   it can mean the dimension is infinite, or just big, or simply unknown / not
  --   considered in the implementation.
  type StaticDimension v :: Maybe Nat
  type StaticDimension v = 'Nothing

  dimensionalityWitness :: DimensionalityWitness v


instance DimensionAware Float   where
  type StaticDimension Float   = 'Just 1
  dimensionalityWitness = IsStaticDimensional
instance DimensionAware Double  where
  type StaticDimension Double  = 'Just 1
  dimensionalityWitness = IsStaticDimensional
instance DimensionAware Int     where
  type StaticDimension Int     = 'Just 1
  dimensionalityWitness = IsStaticDimensional
instance DimensionAware Integer where
  type StaticDimension Integer = 'Just 1
  dimensionalityWitness = IsStaticDimensional
instance Integral n => DimensionAware (Ratio n) where
  type StaticDimension (Ratio n) = 'Just 1
  dimensionalityWitness = IsStaticDimensional

instance ∀ u v . (DimensionAware u, DimensionAware v, Scalar u ~ Scalar v)
                   => DimensionAware (u,v) where
  type StaticDimension (u,v) = Maybe.ZipWithPlus (StaticDimension u) (StaticDimension v)
  dimensionalityWitness = case (dimensionalityWitness @u, dimensionalityWitness @v) of
    (IsStaticDimensional, IsStaticDimensional)
       -> withKnownNat (dimensionalitySing @u %+ dimensionalitySing @v)
              IsStaticDimensional
    (IsFlexibleDimensional, _) -> IsFlexibleDimensional
    (_, IsFlexibleDimensional) -> IsFlexibleDimensional


class (DimensionAware v, StaticDimension v ~ 'Just n)
           => n`Dimensional`v | v -> n where
  knownDimensionalitySing :: Sing n
  {-# INLINE knownDimensionalitySing #-}
  default knownDimensionalitySing :: KnownNat n => Sing n
  knownDimensionalitySing = sing
  -- | Read basis expansion from an array, starting at the specified offset.
  --   The array must have at least length @n + offset@, else the behaviour is undefined.
  unsafeFromArrayWithOffset :: GArr.Vector α (Scalar v) => Int -> α (Scalar v) -> v
  unsafeWriteArrayWithOffset :: GArr.Vector α (Scalar v)
          => GArr.Mutable α σ (Scalar v) -> Int -> v -> ST σ ()

-- | Batteries-included version of 'DimensionalityWitness'.
data DimensionalityCases v where
  StaticDimensionalCase :: (KnownNat n, n`Dimensional`v) => DimensionalityCases v
  FlexibleDimensionalCase :: StaticDimension v ~ 'Nothing => DimensionalityCases v

staticDimensionalIsStatic :: ∀ v n r
     . (DimensionAware v, StaticDimension v ~ 'Just n)
              => (n`Dimensional`v => r) -> r
staticDimensionalIsStatic = case dimensionalityWitness @v of
   IsStaticDimensional -> \φ -> φ

{-# INLINE dimensionalitySing #-}
dimensionalitySing :: ∀ v n . n`Dimensional`v => Sing n
dimensionalitySing = knownDimensionalitySing @n @v

dimensionality :: ∀ v . DimensionAware v => DimensionalityCases v
dimensionality = case dimensionalityWitness @v of
  IsStaticDimensional -> withKnownNat (dimensionalitySing @v) StaticDimensionalCase
  IsFlexibleDimensional -> FlexibleDimensionalCase

{-# INLINE dimension #-}
dimension :: ∀ v n a . (n`Dimensional`v, Integral a) => a
dimension = withKnownNat (dimensionalitySing @v) (fromIntegral $ natVal @n Proxy)

-- | Convenience function. The result does never depend on the runtime input, only
--   on its type.
dimensionOf :: ∀ v n a . (n`Dimensional`v, Integral a) => v -> a
dimensionOf _ = dimension @v

{-# INLINE unsafeFromArray #-}
-- | Read basis expansion from an array. The array must have length @n@, else the
--   behaviour is undefined.
unsafeFromArray :: ∀ v n α . (n`Dimensional`v, GArr.Vector α (Scalar v))
         => α (Scalar v) -> v
unsafeFromArray = unsafeFromArrayWithOffset 0

-- | Read basis expansion from an array, if the size equals the dimension.
fromArray :: ∀ v n α . (n`Dimensional`v, GArr.Vector α (Scalar v))
         => α (Scalar v) -> Maybe v
fromArray ar
 | GArr.length ar == dimension @v  = Just $ unsafeFromArray ar
 | otherwise                       = Nothing

{-# INLINE toArray #-}
-- | Write out basis expansion to an array, whose length will always be @n@.
toArray :: ∀ v n α . (n`Dimensional`v, GArr.Vector α (Scalar v))
         => v -> α (Scalar v)
toArray v = GArr.create (do
   ar <- GMArr.new $ dimension @v
   unsafeWriteArrayWithOffset ar 0 v
   return ar
  )

{-# INLINE staticDimensionSing #-}
staticDimensionSing :: ∀ v . DimensionAware v => Sing (StaticDimension v)
staticDimensionSing = case dimensionalityWitness @v of
  IsStaticDimensional -> sing
  IsFlexibleDimensional -> sing

{-# INLINE scalarUnsafeFromArrayWithOffset #-}
scalarUnsafeFromArrayWithOffset :: (v ~ Scalar v, GArr.Vector α v)
          => Int -> α v -> v
scalarUnsafeFromArrayWithOffset i = (`GArr.unsafeIndex`i)

{-# INLINE scalarUnsafeWriteArrayWithOffset #-}
scalarUnsafeWriteArrayWithOffset :: (v ~ Scalar v, GArr.Vector α v)
          => GArr.Mutable α σ v -> Int -> v -> ST σ ()
scalarUnsafeWriteArrayWithOffset ar i = GMArr.unsafeWrite ar i

{-# INLINE unsafeFromArrayWithOffsetViaList #-}
unsafeFromArrayWithOffsetViaList
          :: ∀ v n α . (n`Dimensional`v, GArr.Vector α (Scalar v))
   => ([Scalar v] -> v) -> Int -> α (Scalar v) -> v
unsafeFromArrayWithOffsetViaList l2v i
   = l2v . GArr.toList . GArr.unsafeSlice i (dimension @v)
  
{-# INLINE unsafeWriteArrayWithOffsetViaList #-}
unsafeWriteArrayWithOffsetViaList
          :: ∀ v n α σ . (n`Dimensional`v, GArr.Vector α (Scalar v))
   => (v -> [Scalar v]) -> GArr.Mutable α σ (Scalar v)
         -> Int -> v -> ST σ ()
unsafeWriteArrayWithOffsetViaList v2l ar i
   = GMArr.unsafeCopy (GMArr.unsafeSlice i (dimension @v) ar)
      <=< GArr.unsafeThaw @(ST σ) @α . GArr.fromList . v2l
  
instance 1`Dimensional`Float   where
  {-# INLINE unsafeFromArrayWithOffset #-}
  unsafeFromArrayWithOffset = scalarUnsafeFromArrayWithOffset
  {-# INLINE unsafeWriteArrayWithOffset #-}
  unsafeWriteArrayWithOffset = scalarUnsafeWriteArrayWithOffset
instance 1`Dimensional`Double  where
  {-# INLINE unsafeFromArrayWithOffset #-}
  unsafeFromArrayWithOffset = scalarUnsafeFromArrayWithOffset
  {-# INLINE unsafeWriteArrayWithOffset #-}
  unsafeWriteArrayWithOffset = scalarUnsafeWriteArrayWithOffset
instance 1`Dimensional`Int     where
  {-# INLINE unsafeFromArrayWithOffset #-}
  unsafeFromArrayWithOffset = scalarUnsafeFromArrayWithOffset
  {-# INLINE unsafeWriteArrayWithOffset #-}
  unsafeWriteArrayWithOffset = scalarUnsafeWriteArrayWithOffset
instance 1`Dimensional`Integer where
  {-# INLINE unsafeFromArrayWithOffset #-}
  unsafeFromArrayWithOffset = scalarUnsafeFromArrayWithOffset
  {-# INLINE unsafeWriteArrayWithOffset #-}
  unsafeWriteArrayWithOffset = scalarUnsafeWriteArrayWithOffset
instance Integral n => 1`Dimensional`Ratio n where
  {-# INLINE unsafeFromArrayWithOffset #-}
  unsafeFromArrayWithOffset = scalarUnsafeFromArrayWithOffset
  {-# INLINE unsafeWriteArrayWithOffset #-}
  unsafeWriteArrayWithOffset = scalarUnsafeWriteArrayWithOffset

  
instance ∀ n u m v nm . ( n`Dimensional`u, m`Dimensional`v
                        , Scalar u ~ Scalar v
                        , nm ~ (n+m) )
                   => nm`Dimensional`(u,v) where
  {-# INLINE knownDimensionalitySing #-}
  knownDimensionalitySing = dimensionalitySing @u %+ dimensionalitySing @v
  {-# INLINE unsafeFromArrayWithOffset #-}
  unsafeFromArrayWithOffset i arr
      = ( unsafeFromArrayWithOffset i arr
        , unsafeFromArrayWithOffset (i + dimension @u) arr )
  {-# INLINE unsafeWriteArrayWithOffset #-}
  unsafeWriteArrayWithOffset arr i (x,y) = do
      unsafeWriteArrayWithOffset arr i x
      unsafeWriteArrayWithOffset arr (i + dimension @u) y

type family FromJust (a :: Maybe k) :: k where
  FromJust ('Just v) = v

type StaticallyKnownDimension v = FromJust (StaticDimension v)

notStaticDimensionalContradiction :: ∀ v n r
  . (n`Dimensional`v, StaticDimension v ~ 'Nothing) => r
notStaticDimensionalContradiction = undefined

