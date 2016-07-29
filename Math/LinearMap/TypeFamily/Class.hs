-- |
-- Module      : Math.LinearMap.TypeFamily.Class
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UnicodeSyntax              #-}

module Math.LinearMap.TypeFamily.Class (LinearSpace (..)) where

import Data.VectorSpace

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained



class VectorSpace v => LinearSpace v where
  data (-→) v w :: *
  linearId :: v -→ v
  zeroMapping :: (LinearSpace w, Scalar w ~ Scalar v) => v -→ w
  addLinearMaps :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v -→ w) -> (v -→ w) -> v -→ w
  negateLinearMap :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v -→ w) -> v -→ w
  linearCoFst :: (LinearSpace w, Scalar w ~ Scalar v)
                => v -→ (v,w)
  linearCoSnd :: (LinearSpace w, Scalar w ~ Scalar v)
                => v -→ (w,v)
  fanoutBlocks :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v-→w) -> (v-→x) -> v -→ (w,x)
  firstBlock :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => v -→ w -> v -→ (w,x)
  secondBlock :: ( LinearSpace w, LinearSpace x
                      , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => v -→ x -> v -→ (w,x)
  applyLinear :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v -→ w) -> v -> w
  composeLinear :: ( LinearSpace w, LinearSpace x
                   , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => w -→ x -> v -→ w -> v -→ x



data ZeroDim s = Origin
instance Monoid (ZeroDim s) where
  mempty = Origin
  mappend Origin Origin = Origin

instance AdditiveGroup (ZeroDim s) where
  zeroV = Origin
  Origin ^+^ Origin = Origin
  negateV Origin = Origin
instance VectorSpace (ZeroDim s) where
  type Scalar (ZeroDim s) = s
  _ *^ Origin = Origin
instance LinearSpace (ZeroDim s) where
  data ZeroDim s -→ v = CoOrigin
  linearId = CoOrigin
  zeroMapping = CoOrigin
  negateLinearMap CoOrigin = CoOrigin
  addLinearMaps CoOrigin CoOrigin = CoOrigin
  linearCoFst = CoOrigin
  linearCoSnd = CoOrigin
  fanoutBlocks CoOrigin CoOrigin = CoOrigin
  firstBlock CoOrigin = CoOrigin
  secondBlock CoOrigin = CoOrigin
  applyLinear _ _ = zeroV
  composeLinear _ _ = CoOrigin


newtype LinearMap s v w = LinearMap {getLinearMap :: v -→ w}

instance (LinearSpace v, LinearSpace w, Scalar v~s, Scalar w~s)
               => AdditiveGroup (LinearMap s v w) where
  zeroV = LinearMap zeroMapping
  LinearMap f ^+^ LinearMap g = LinearMap $ addLinearMaps f g
  negateV (LinearMap f) = LinearMap $ negateLinearMap f

instance Category (LinearMap s) where
  type Object (LinearMap s) v = (LinearSpace v, Scalar v ~ s)
  id = LinearMap linearId
  LinearMap f . LinearMap g = LinearMap $ composeLinear f g
instance Cartesian (LinearMap s) where
  type UnitObject (LinearMap s) = ZeroDim s
  swap = LinearMap $ CoDirectSum linearCoSnd linearCoFst
  attachUnit = LinearMap linearCoFst
  detachUnit = LinearMap $ CoDirectSum linearId zeroMapping
  regroup = LinearMap $ CoDirectSum (composeLinear linearCoFst linearCoFst)
                                    (CoDirectSum (composeLinear linearCoFst linearCoSnd)
                                                 linearCoSnd )
  regroup' = LinearMap $ CoDirectSum (CoDirectSum linearCoFst
                                                  (composeLinear linearCoSnd linearCoFst))
                                     (composeLinear linearCoSnd linearCoSnd)
instance Morphism (LinearMap s) where
  LinearMap f *** LinearMap g
      = LinearMap $ CoDirectSum (firstBlock f) (secondBlock g)
instance PreArrow (LinearMap s) where
  LinearMap f &&& LinearMap g = LinearMap $ fanoutBlocks f g
  terminal = zeroV
  fst = LinearMap $ CoDirectSum linearId zeroMapping
  snd = LinearMap $ CoDirectSum zeroMapping linearId

type ℝ = Double

instance LinearSpace ℝ where
  data ℝ -→ w = RealVect w
  linearId = RealVect 1
  zeroMapping = RealVect zeroV
  addLinearMaps (RealVect v) (RealVect w) = RealVect $ v ^+^ w
  negateLinearMap (RealVect w) = RealVect $ negateV w
  linearCoFst = RealVect (1, zeroV)
  linearCoSnd = RealVect (zeroV, 1)
  fanoutBlocks (RealVect v) (RealVect w) = RealVect (v,w)
  firstBlock (RealVect v) = RealVect (v,zeroV)
  secondBlock (RealVect w) = RealVect (zeroV,w)
  applyLinear (RealVect w) μ = μ *^ w
  composeLinear f (RealVect w) = RealVect $ applyLinear f w

instance ∀ u v . (LinearSpace u, LinearSpace v, Scalar u ~ Scalar v)
                       => LinearSpace (u,v) where
  data (u,v) -→ w = CoDirectSum !(u-→w) !(v-→w)
  linearId = CoDirectSum linearCoFst linearCoSnd
  zeroMapping = CoDirectSum zeroMapping zeroMapping
  addLinearMaps (CoDirectSum fu fv) (CoDirectSum fu' fv')
      = CoDirectSum (addLinearMaps fu fu') (addLinearMaps fv fv')
  negateLinearMap (CoDirectSum fu fv)
      = CoDirectSum (negateLinearMap fu) (negateLinearMap fv)
  linearCoFst = CoDirectSum (composeLinear linearCoFst linearCoFst)
                            (composeLinear linearCoFst linearCoSnd)
  linearCoSnd = CoDirectSum (composeLinear linearCoSnd linearCoFst)
                            (composeLinear linearCoSnd linearCoSnd)
  fanoutBlocks (CoDirectSum fu fv) (CoDirectSum gu gv)
              = CoDirectSum (fanoutBlocks fu gu) (fanoutBlocks fv gv)
  firstBlock (CoDirectSum fu fv) = CoDirectSum (firstBlock fu) (firstBlock fv)
  secondBlock (CoDirectSum fu fv) = CoDirectSum (secondBlock fu) (secondBlock fv)
  applyLinear (CoDirectSum fu fv) (u,v) = applyLinear fu u ^+^ applyLinear fv v
  composeLinear f (CoDirectSum fu fv)
        = CoDirectSum (composeLinear f fu) (composeLinear f fv)


    
