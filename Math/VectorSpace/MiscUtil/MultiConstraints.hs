-- |
-- Module      : Math.VectorSpace.MiscUtil.MultiConstraints
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE UndecidableInstances  #-}

module Math.VectorSpace.MiscUtil.MultiConstraints
    ( SameScalar
    ) where

import Data.VectorSpace
import Data.Kind (Type)
import GHC.Exts (Constraint)


type family AllWithScalar (s :: Type) (c :: Type -> Constraint) (vs :: [Type])
              :: Constraint where
  AllWithScalar s c '[] = ()
  AllWithScalar s c (v ': vs) = (c v, Scalar v ~ s, AllWithScalar s c vs)

type family SameScalar (c :: Type -> Constraint) (vs :: [Type]) :: Constraint where
  SameScalar c '[] = ()
  SameScalar c (v ': vs)
      = (c v, AllWithScalar (Scalar v) c vs)
