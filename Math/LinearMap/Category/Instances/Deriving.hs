-- |
-- Module      : Math.LinearMap.Instances.Deriving
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE CPP                        #-}

module Math.LinearMap.Category.Instances.Deriving where

import Math.LinearMap.Category.Class

import Data.VectorSpace
import Data.AffineSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Coerce
import Data.Type.Coercion
import Data.Tagged

import Math.Manifold.Core.PseudoAffine
import Math.LinearMap.Asserted
import Math.VectorSpace.ZeroDimensional
import Data.VectorSpace.Free

import Language.Haskell.TH


makeTensorSpaceFromBasis :: Q Type -> DecsQ
makeTensorSpaceFromBasis v = do
  semiMfdInst <- InstanceD Nothing [] <$> [t|Semimanifold $v|] <*> do
    tySyns <- sequence [
#if MIN_VERSION_template_haskell(2,15,0)
       error "The TH type of TySynInstD has changed"
#else
       TySynInstD ''Needle <$> do
         TySynEqn . (:[]) <$> v <*> v
     , TySynInstD ''Interior <$> do
         TySynEqn . (:[]) <$> v <*> v
#endif
     ]
    methods <- [d|
        $(varP $ mkName "toInterior") = pure
        $(varP $ mkName "fromInterior") = id
        $(varP $ mkName "translateP") = Tagged (^+^)
        $(varP $ mkName ".+~^") = (^+^)
        $(varP $ mkName "semimanifoldWitness") = SemimanifoldWitness BoundarylessWitness
     |]
    return $ tySyns ++ methods
  return [ semiMfdInst
         ]

newtype SpaceFromBasis v = SpaceFromBasis { getSpaceFromBasis :: v }
  deriving newtype (AdditiveGroup, VectorSpace, HasBasis)

instance AdditiveGroup v => Semimanifold (SpaceFromBasis v) where
  type Needle (SpaceFromBasis v) = SpaceFromBasis v
  type Interior (SpaceFromBasis v) = SpaceFromBasis v
  toInterior = pure
  fromInterior = id
  translateP = Tagged (^+^)
  (.+~^) = (^+^)
  semimanifoldWitness = SemimanifoldWitness BoundarylessWitness


