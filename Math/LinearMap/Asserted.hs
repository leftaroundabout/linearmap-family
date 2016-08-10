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
import Data.Traversable.Constrained

import Data.Coerce
import Data.Type.Coercion

import Data.VectorSpace.Free
import Math.VectorSpace.ZeroDimensional
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

instance Traversable V0 V0 LinearFunction LinearFunction where
  traverse (LinearFunction _)
      = fmap (LinearFunction $ const V0) . pureUnit . LinearFunction (const ())
  sequence = fmap (LinearFunction $ const V0) . pureUnit . LinearFunction (const ())
instance Traversable V1 V1 LinearFunction LinearFunction where
  traverse (LinearFunction f) = LinearFunction $ \(V1 x) -> fmap (LinearFunction V1) $ f x
  sequence = LinearFunction $ \(V1 q) -> fmap (LinearFunction V1) $ q
instance Traversable V2 V2 LinearFunction LinearFunction where
  traverse (LinearFunction f) = LinearFunction $ \(V2 x y)
               -> fzipWith (LinearFunction $ \(fx,fy) -> V2 fx fy) $ (f x, f y)
  sequence = LinearFunction $ \(V2 p q) -> fzipWith (LinearFunction $ uncurry V2) $ (p,q)
instance Traversable V3 V3 LinearFunction LinearFunction where
  traverse (LinearFunction f) = LinearFunction $ \(V3 x y z)
               -> fzipWith (LinearFunction $ \(fx,V2 fy fz) -> V3 fx fy fz)
                       $ (f x, traverse (LinearFunction f) $ V2 y z)
  sequence = LinearFunction $ \(V3 p q r)
               -> fzipWith (LinearFunction $ \(sp,V2 sq sr) -> V3 sp sq sr)
                       $ (p, getLinearFunction sequence $ V2 q r)
instance Traversable V4 V4 LinearFunction LinearFunction where
  traverse f = LinearFunction $ \(V4 x y z w)
               -> fzipWith (LinearFunction $ \(V2 fx fy,V2 fz fw) -> V4 fx fy fz fw)
                       $ ( traverse f $ (V2 x y), traverse f $ (V2 z w))
  sequence = LinearFunction $ \(V4 p q r s)
               -> fzipWith (LinearFunction $ \(V2 sp sq,V2 sr ss) -> V4 sp sq sr ss)
                       $ ( getLinearFunction sequence $ V2 p q
                         , getLinearFunction sequence $ V2 r s )
