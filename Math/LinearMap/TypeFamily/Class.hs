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
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ConstraintKinds            #-}
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


type Num' s = (Num s, VectorSpace s, Scalar s ~ s)

class (VectorSpace v, Num' (Scalar v)) => LinearSpace v where
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
     => (v-→w) -> v -→ (w,x)
  secondBlock :: ( LinearSpace w, LinearSpace x
                      , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => (v-→x) -> v -→ (w,x)
  applyLinear :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v -→ w) -> v -> w
  composeLinear :: ( LinearSpace w, LinearSpace x
                   , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => (w -→ x) -> (v -→ w) -> v -→ x



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
instance Num' s => LinearSpace (ZeroDim s) where
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
instance Num' s => Cartesian (LinearMap s) where
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
instance Num' s => Morphism (LinearMap s) where
  LinearMap f *** LinearMap g
      = LinearMap $ CoDirectSum (firstBlock f) (secondBlock g)
instance Num' s => PreArrow (LinearMap s) where
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

type DualSpace v = v -→ Scalar v

type Fractional' s = (Fractional s, VectorSpace s, Scalar s ~ s)

class (LinearSpace v, LinearSpace (Scalar v)) => SemiInner v where
  {-# MINIMAL orthogonalise | orthogonalPart #-} 
--   -- | Contrary to common belief, /vector division/ is actually quite a useful
--   --   operation and in fact more general than the ubiquitous inner product.
--   --   Like scalar division this is partial, i.e. @v ^/^ zeroV@ is undefined.
--   --   Laws for @v,w ≠ zeroV@:
--   --   @
--   --   v ^/^ v ≡ 1
--   --   @
--   --   @
--   --   (ν*^u + μ*^v) ^/^ w ≡ ν * (u^/w) + μ * (v^/^w)
--   --   @
--   --   On inner-product spaces, @v^/^w ≡ (v<.>w)/(w<.>w)@.
--   (^/^) :: v -> v -> Scalar v
--   v^/^v₁ = applyLinear (recipV v₁) v
-- 
-- -- (v ^/^ w) ⋅ (w ^/^ v)
-- --   = ⟨v|w)/⟨w|w⟩ ⋅ ⟨w|v⟩/⟨v|v⟩
-- -- (v ^/^ w) / (w ^/^ v)
-- --   = ⟨v|w)/⟨w|w⟩ / ⟨w|v⟩/⟨v|v⟩
-- --   = ⟨v|v)/⟨w|w⟩
--   
--   recipV :: v -> DualSpace v
  
  -- | If @(u',v') = orthogonalise u v@, then
  --   @
  --   u' ^+^ v' ≡ u ^+^ v
  --   @
  --   @
  --   u' ^/^ v' ≡ 0
  --   @
  orthogonalise :: v -> v -> (v,v)
  orthogonalise u v = (u^+^v^-^v', v')
   where v' = orthogonalPart u v
  orthogonalPart :: v -> v -> v
  orthogonalPart u v = snd (orthogonalise u v)

instance (Fractional' s, SemiInner s) => SemiInner (ZeroDim s) where
--   Origin ^/^ Origin = 0  -- Not really sensible of course; actually (^/^) is
--                          -- /always undefined/ on 'ZeroDim' space. 1 might be
--                          -- a more reasonable result, but it would disagree
--                          -- with the 'recipV' induced one.
--   recipV Origin = CoOrigin
  orthogonalise Origin Origin = (Origin, Origin)

instance SemiInner ℝ where
--   (^/^) = (/)
--   recipV = RealVect . recip
  orthogonalise n m = (n+m, 0)

instance (SemiInner u, SemiInner v, Scalar u ~ Scalar v) => SemiInner (u,v) where
  orthogonalise (u₀,v₀) (u₁,v₁) = ((u₀^+^u₁, zeroV), (zeroV, v₀^+^v₁))
  

class LinearSpace v => LeastSquares v where
  splitOffDependent :: v -> v -> (Scalar v, v)
  coRiesz :: DualSpace v -> (v, Scalar v)
  leastSquareSolve :: (LeastSquares w, Scalar w~Scalar v)
            => (w-→v) -> v->w
  pseudoInverse :: (LeastSquares w, Scalar w~Scalar v)
            => (w-→v) -> v-→w


instance Num' s => LeastSquares (ZeroDim s) where
  splitOffDependent Origin Origin = (1, Origin)
  coRiesz CoOrigin = (Origin, 0)
  leastSquareSolve _ _ = zeroV
  pseudoInverse _ = zeroMapping
  
instance LeastSquares ℝ where
  splitOffDependent r s = (r/s, 0)
  coRiesz (RealVect r) = (r, r^2)
  leastSquareSolve m μ = (μ/νu) *^ u
   where (u,νu) = coRiesz m
  pseudoInverse m = RealVect $ u ^/ νu
   where (u,νu) = coRiesz m
  
instance ( LeastSquares u, SemiInner u, LeastSquares v, SemiInner v
         , Scalar u ~ Scalar v )
            => LeastSquares (u,v) where
  -- splitOffDependent (u,v) (u₁,v₁) = case (splitOffDependent u u₁, spl0
  coRiesz (CoDirectSum fu fv) = ((u,v), νu+νv)
   where (u,νu) = coRiesz fu
         (v,νv) = coRiesz fv
  leastSquareSolve m (u,v) = m'u ^+^ m'v ^-^ m'v'u ^-^ m'u'v
   where mdu = composeLinear (CoDirectSum linearId zeroMapping) m
         mdv = composeLinear (CoDirectSum zeroMapping linearId) m
         m'u = leastSquareSolve mdu u
         m'v = leastSquareSolve mdv v
         (u'v,_) = applyLinear m m'v
         (_,v'u) = applyLinear m m'u
         m'u'v = leastSquareSolve mdu u'v
         m'v'u = leastSquareSolve mdv v'u
  -- pseudoInverse m = RealVect $ coRiesz m
    
