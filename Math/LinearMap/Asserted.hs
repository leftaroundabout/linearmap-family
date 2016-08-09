-- |
-- Module      : Math.LinearMap.Asserted
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
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Math.LinearMap.Asserted where

import Data.VectorSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion

import Data.VectorSpace.Free
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat




newtype LinearFunction v w = LinearFunction { getLinearFunction :: v -> w }



instance Category LinearFunction where
  id = LinearFunction id
  LinearFunction f . LinearFunction g = LinearFunction $ f.g
instance Cartesian LinearFunction where
  swap = LinearFunction swap
  attachUnit = LinearFunction attachUnit; detachUnit = LinearFunction detachUnit
  regroup = LinearFunction regroup; regroup' = LinearFunction regroup'
instance Morphism LinearFunction where
  LinearFunction f***LinearFunction g = LinearFunction $ f***g
instance PreArrow LinearFunction where
  LinearFunction f&&&LinearFunction g = LinearFunction $ f&&&g
  fst = LinearFunction fst; snd = LinearFunction snd
  terminal = LinearFunction terminal
instance EnhancedCat (->) LinearFunction where
  arr = getLinearFunction
instance EnhancedCat LinearFunction Coercion where
  arr = LinearFunction . coerceWith

scaleWith :: VectorSpace v => Scalar v -> LinearFunction v v
scaleWith μ = LinearFunction (μ*^)

scaleV :: VectorSpace v => v -> LinearFunction (Scalar v) v
scaleV v = LinearFunction (*^v)

const0 :: AdditiveGroup v => LinearFunction v v
const0 = LinearFunction (const zeroV)


#define FreeLinFtor(V)                                  \
instance Functor V LinearFunction LinearFunction where   \
  fmap (LinearFunction f) = LinearFunction $ fmap f

FreeLinFtor(V0)
FreeLinFtor(V1)
FreeLinFtor(V2)
FreeLinFtor(V3)
FreeLinFtor(V4)

