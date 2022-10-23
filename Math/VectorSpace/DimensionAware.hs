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

import GHC.TypeLits

import Data.Ratio

import qualified Math.VectorSpace.DimensionAware.Theorems.MaybeNat as Maybe


data DimensionalityWitness v where
  IsStaticDimensional :: n`Dimensional`v => DimensionalityWitness v
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


class (DimensionAware v, KnownNat n, StaticDimension v ~ 'Just n)
           => n`Dimensional`v | v -> n

dimensionalitySing :: ∀ v n . n`Dimensional`v => Sing n
dimensionalitySing = sing

staticDimensionSing :: ∀ v . DimensionAware v => Sing (StaticDimension v)
staticDimensionSing = case dimensionalityWitness @v of
  IsStaticDimensional -> sing
  IsFlexibleDimensional -> sing
  
instance 1`Dimensional`Float   where
instance 1`Dimensional`Double  where
instance 1`Dimensional`Int     where
instance 1`Dimensional`Integer where
instance Integral n => 1`Dimensional`Ratio n where

  
instance ∀ n u m v nm . ( n`Dimensional`u, m`Dimensional`v
                        , Scalar u ~ Scalar v
                        , KnownNat nm
                        , nm ~ (n+m) )
                   => nm`Dimensional`(u,v) where

type family FromJust (a :: Maybe k) :: k where
  FromJust ('Just v) = v

type StaticallyKnownDimension v = FromJust (StaticDimension v)

