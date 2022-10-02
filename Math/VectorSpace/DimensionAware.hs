-- |
-- Module      : Math.VectorSpace.DimensionAware
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE ScopedTypeVariables  #-}

module Math.VectorSpace.DimensionAware where

import Data.VectorSpace

import Data.Singletons (SingI, sing, Sing)

import GHC.TypeLits

import qualified Math.VectorSpace.DimensionAware.Theorems.MaybeNat as Maybe

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

  staticDimensionSing :: Sing (StaticDimension v)
  default staticDimensionSing :: SingI (StaticDimension v)
               => Sing (StaticDimension v)
  staticDimensionSing = sing


instance DimensionAware Float   where type StaticDimension Float   = 'Just 1
instance DimensionAware Double  where type StaticDimension Double  = 'Just 1
instance DimensionAware Int     where type StaticDimension Int     = 'Just 1
instance DimensionAware Integer where type StaticDimension Integer = 'Just 1

instance ∀ u v . (DimensionAware u, DimensionAware v, Scalar u ~ Scalar v)
                   => DimensionAware (u,v) where
  type StaticDimension (u,v) = Maybe.ZipWithPlus (StaticDimension u) (StaticDimension v)
  staticDimensionSing = Maybe.zipWithPlusSing (staticDimensionSing @u)
                                              (staticDimensionSing @v)

