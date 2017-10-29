-- |
-- Module      : Math.LinearMap.Category.TensorQuot
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE CPP                   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UnicodeSyntax         #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ConstraintKinds       #-}

module Math.LinearMap.Category.TensorQuot where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted

import Data.VectorSpace
import Data.VectorSpace.Free

infixl 7 ·

class (TensorSpace v, TensorSpace w) => TensorQuot v w where
  type v ⨸ w :: *
  -- | Generalised multiplication operation. This subsumes '<.>^' and '*^'.
  --   For scalars therefore also '*', and for 'InnerSpace', '<.>'.
  (·) :: v ⨸ w -> v -> w

instance TensorQuot Double Double where
  type Double ⨸ Double = Double
  (·) = (*)

instance ( TensorQuot x v, TensorQuot y w
         , Scalar x ~ Scalar y, Scalar v ~ Scalar w
         , (x⨸v) ~ (y⨸w) )
      => TensorQuot (x,y) (v,w) where
  type (x,y) ⨸ (v,w) = x⨸v
  μ·(x,y) = (μ·x, μ·y)
instance ( TensorQuot x Double, TensorQuot y Double
         , Scalar x ~ Double, Scalar y ~ Double )
      => TensorQuot (x,y) Double where
  type (x,y) ⨸ Double = (x ⨸ Double, y ⨸ Double)
  (v,w)·(x,y) = v·x + w·y

#define FreeTensorQuot(V)                                \
instance (Num' s, Eq s) => TensorQuot (V s) (V s) where { \
  type V s ⨸ V s = s;                                      \
  (·) = (*^) };                                             \
instance TensorQuot (V Double) Double where {                \
  type V Double ⨸ Double = V Double;                          \
  (·) = (<.>) }

FreeTensorQuot(V1)
FreeTensorQuot(V2)
FreeTensorQuot(V3)
FreeTensorQuot(V4)
