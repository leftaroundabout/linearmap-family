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
{-# LANGUAGE TupleSections              #-}

module Math.LinearMap.TypeFamily.Class (LinearSpace (..)) where

import Data.VectorSpace

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Tree (Tree(..), Forest)
import Data.List (sortBy)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Ord (comparing)

type Num' s = (Num s, VectorSpace s, Scalar s ~ s)

class (VectorSpace v, Num' (Scalar v)) => LinearSpace v where
  data (-→) v w :: *
  linearId :: v -→ v
  zeroMapping :: (LinearSpace w, Scalar w ~ Scalar v) => v -→ w
  addLinearMaps :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v -→ w) -> (v -→ w) -> v -→ w
  subtractLinearMaps :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v -→ w) -> (v -→ w) -> v -→ w
  subtractLinearMaps m n = addLinearMaps m (negateLinearMap n)
  scaleLinearMap :: (LinearSpace w, Scalar w ~ Scalar v)
                => Scalar v -> (v -→ w) -> v -→ w
  negateLinearMap :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v -→ w) -> v -→ w
  linearCoFst :: (LinearSpace w, Scalar w ~ Scalar v)
                => v -→ (v,w)
  linearCoSnd :: (LinearSpace w, Scalar w ~ Scalar v)
                => v -→ (w,v)
  fanoutBlocks :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v-→w) -> (v-→x) -> v -→ (w,x)
  fstBlock :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v-→(w,x)) -> v -→ w
  sndBlock :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v-→(w,x)) -> v -→ x
  sepBlocks :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v-→(w,x)) -> (v-→w, v-→x)
  sepBlocks m = (fstBlock m, sndBlock m)
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
  scaleLinearMap _ CoOrigin = CoOrigin
  addLinearMaps CoOrigin CoOrigin = CoOrigin
  linearCoFst = CoOrigin
  linearCoSnd = CoOrigin
  fstBlock CoOrigin = CoOrigin
  sndBlock CoOrigin = CoOrigin
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
  LinearMap f ^-^ LinearMap g = LinearMap $ subtractLinearMaps f g
  negateV (LinearMap f) = LinearMap $ negateLinearMap f
instance (LinearSpace v, LinearSpace w, Scalar v~s, Scalar w~s)
               => VectorSpace (LinearMap s v w) where
  type Scalar (LinearMap s v w) = s
  μ *^ LinearMap f = LinearMap $ scaleLinearMap μ f
instance Num (LinearMap ℝ ℝ ℝ) where
  fromInteger = LinearMap . RealVect . fromInteger
  (+) = (^+^)
  (-) = (^-^)
  LinearMap (RealVect m) * LinearMap (RealVect n)
         = LinearMap . RealVect $ m*n
  abs (LinearMap (RealVect n)) = LinearMap . RealVect $ abs n
  signum (LinearMap (RealVect n)) = LinearMap . RealVect $ signum n
instance Fractional (LinearMap ℝ ℝ ℝ) where
  fromRational = LinearMap . RealVect . fromRational
  LinearMap (RealVect m) / LinearMap (RealVect n)
         = LinearMap . RealVect $ m/n
  recip (LinearMap (RealVect n)) = LinearMap . RealVect $ recip n
  
infixr 6 ⊕, >+<
(⊕), (>+<) :: LinearMap s u w -> LinearMap s v w -> LinearMap s (u,v) w
LinearMap m ⊕ LinearMap n = LinearMap $ CoDirectSum m n
(>+<) = (⊕)

instance Show (LinearMap ℝ ℝ ℝ) where
  show (LinearMap (RealVect n)) = show n
instance ∀ u v . (Show (LinearMap ℝ u ℝ), Show (LinearMap ℝ v ℝ))
           => Show (LinearMap ℝ (u,v) ℝ) where
  showsPrec p (LinearMap (CoDirectSum m n))
        = showParen (p>6)
            (showsPrec 6 (LinearMap m :: LinearMap ℝ u ℝ)
                         . ("⊕"++) . showsPrec 6 (LinearMap n :: LinearMap ℝ v ℝ))
instance ∀ s u v w . ( LinearSpace u, LinearSpace v, LinearSpace w
                     , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
                     , Show (LinearMap s u v), Show (LinearMap s u w) )
           => Show (LinearMap s u (v,w)) where
  showsPrec p (LinearMap m)
        = showParen (p>6)
            (showsPrec 6 (LinearMap mv :: LinearMap s u v)
                         . (" &&& "++) . showsPrec 6 (LinearMap mw :: LinearMap s u w))
   where (mv, mw) = sepBlocks m

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
instance Num' s => EnhancedCat (->) (LinearMap s) where
  arr (LinearMap m) = applyLinear m

type ℝ = Double

instance LinearSpace ℝ where
  data ℝ -→ w = RealVect w
  linearId = RealVect 1
  zeroMapping = RealVect zeroV
  scaleLinearMap μ (RealVect v) = RealVect $ μ *^ v
  addLinearMaps (RealVect v) (RealVect w) = RealVect $ v ^+^ w
  negateLinearMap (RealVect w) = RealVect $ negateV w
  linearCoFst = RealVect (1, zeroV)
  linearCoSnd = RealVect (zeroV, 1)
  fstBlock (RealVect (u, v)) = RealVect u
  sndBlock (RealVect (u, v)) = RealVect v
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
  scaleLinearMap μ (CoDirectSum fu fv)
      = CoDirectSum (scaleLinearMap μ fu) (scaleLinearMap μ fv)
  addLinearMaps (CoDirectSum fu fv) (CoDirectSum fu' fv')
      = CoDirectSum (addLinearMaps fu fu') (addLinearMaps fv fv')
  negateLinearMap (CoDirectSum fu fv)
      = CoDirectSum (negateLinearMap fu) (negateLinearMap fv)
  linearCoFst = CoDirectSum (composeLinear linearCoFst linearCoFst)
                            (composeLinear linearCoFst linearCoSnd)
  linearCoSnd = CoDirectSum (composeLinear linearCoSnd linearCoFst)
                            (composeLinear linearCoSnd linearCoSnd)
  fstBlock (CoDirectSum fu fv) = CoDirectSum (fstBlock fu) (fstBlock fv)
  sndBlock (CoDirectSum fu fv) = CoDirectSum (sndBlock fu) (sndBlock fv)
  sepBlocks (CoDirectSum fu fv) = (CoDirectSum fuw fvw, CoDirectSum fux fvx)
   where (fuw,fux) = sepBlocks fu
         (fvw,fvx) = sepBlocks fv
  fanoutBlocks (CoDirectSum fu fv) (CoDirectSum gu gv)
              = CoDirectSum (fanoutBlocks fu gu) (fanoutBlocks fv gv)
  firstBlock (CoDirectSum fu fv) = CoDirectSum (firstBlock fu) (firstBlock fv)
  secondBlock (CoDirectSum fu fv) = CoDirectSum (secondBlock fu) (secondBlock fv)
  applyLinear (CoDirectSum fu fv) (u,v) = applyLinear fu u ^+^ applyLinear fv v
  composeLinear f (CoDirectSum fu fv)
        = CoDirectSum (composeLinear f fu) (composeLinear f fv)

lfstBlock :: ( LinearSpace u, LinearSpace v, LinearSpace w
             , Scalar u ~ Scalar v, Scalar v ~ Scalar w )
          => (u-→w) -> (u,v)-→w
lfstBlock f = CoDirectSum f zeroMapping
lsndBlock :: ( LinearSpace u, LinearSpace v, LinearSpace w
            , Scalar u ~ Scalar v, Scalar v ~ Scalar w )
          => (v-→w) -> (u,v)-→w
lsndBlock f = CoDirectSum zeroMapping f

type DualSpace v = v -→ Scalar v

type Fractional' s = (Fractional s, Eq s, VectorSpace s, Scalar s ~ s)

class (LinearSpace v, LinearSpace (Scalar v)) => SemiInner v where
  dualBasis :: [(Int,v)] -> Forest (Int, DualSpace v)
--  coDualBasis :: [(i,DualSpace v)] -> [(i,v)]

instance (Fractional' s, SemiInner s) => SemiInner (ZeroDim s) where
  dualBasis _ = []

instance SemiInner ℝ where
--   (^/^) = (/)
--   recipV = RealVect . recip
  dualBasis = fmap ((`Node`[]) . second (RealVect . recip))
                . sortBy (comparing $ abs . snd)

instance (SemiInner u, SemiInner v, Scalar u ~ Scalar v) => SemiInner (u,v) where
  dualBasis = fmap (\(i,(u,v))->((i,u),(i,v))) >>> unzip
              >>> dualBasis *** dualBasis >>> combineBaseis False (mempty :: Set Int)
   where combineBaseis _ forbidden (bu, []) = combineBaseis False forbidden (bu,[])
         combineBaseis _ forbidden ([], bv) = combineBaseis True forbidden ([],bv)
         combineBaseis False forbidden (Node (i,du) bu' : abu, bv)
            | i`Set.member`forbidden  = combineBaseis False forbidden (abu, bv)
            | otherwise
                 = Node (i, lfstBlock du)
                        (combineBaseis True (Set.insert i forbidden) (bu', bv))
                       : combineBaseis False forbidden (abu, bv)
         combineBaseis True forbidden (bu, Node (i,dv) bv' : abv)
            | i`Set.member`forbidden  = combineBaseis True forbidden (bu, abv)
            | otherwise
                 = Node (i, lsndBlock dv)
                        (combineBaseis False (Set.insert i forbidden) (bu, bv'))
                       : combineBaseis True forbidden (bu, abv)
  
(^/^) :: (InnerSpace v, Eq (Scalar v), Fractional (Scalar v)) => v -> v -> Scalar v
v^/^w = case (v<.>w) of
   0 -> 0
   vw -> vw / (w<.>w)

class LinearSpace v => LeastSquares v where
  splitOffDependent :: v -> v -> (Scalar v, v)
  coRiesz :: DualSpace v -> (v, Scalar v)
  nullSpaceProject :: (LeastSquares w, Scalar w~Scalar v)
            => (w-→v) -> w->w
  preLeastSquareSolve :: (LeastSquares w, Scalar w~Scalar v)
            => (w-→v) -> v->w
  preLeastSquareSolve = leastSquareSolve
  leastSquareSolve :: (LeastSquares w, Scalar w~Scalar v)
            => (w-→v) -> v->w
  leastSquareApproach :: (LeastSquares w, Scalar w~Scalar v)
            => (w-→v) -> v->[w]
  leastSquareApproach m
      = \v -> iterate (\w -> let v' = applyLinear m w
                             in w ^+^ preLeastSquareSolve m (v^-^v') )
                  $ preLeastSquareSolve m v
   where plss = preLeastSquareSolve m
  pseudoInverse :: (LeastSquares w, Scalar w~Scalar v)
            => (w-→v) -> v-→w


instance Num' s => LeastSquares (ZeroDim s) where
  splitOffDependent Origin Origin = (1, Origin)
  nullSpaceProject _ _ = zeroV
  coRiesz CoOrigin = (Origin, 0)
  leastSquareSolve _ _ = zeroV
  pseudoInverse _ = zeroMapping
  
instance LeastSquares ℝ where
  splitOffDependent r s = (r/s, 0)
  coRiesz (RealVect r) = (r, r^2)
  nullSpaceProject f = \v -> v ^-^ f' ^* (applyLinear f v / νf)
   where (f',νf) = coRiesz f
  leastSquareSolve m μ = (μ/νu) *^ u
   where (u,νu) = coRiesz m
  pseudoInverse m = RealVect $ u ^/ νu
   where (u,νu) = coRiesz m
  
instance ( LeastSquares u, InnerSpace u, LeastSquares v, InnerSpace v
         , Scalar u ~ Scalar v, Fractional' (Scalar v) )
            => LeastSquares (u,v) where
  -- splitOffDependent (u,v) (u₁,v₁) = case (splitOffDependent u u₁, spl0
  nullSpaceProject f = nullSpaceProject fu . nullSpaceProject fv
   where (fu, fv) = sepBlocks f
  coRiesz (CoDirectSum fu fv) = ((u,v), νu+νv)
   where (u,νu) = coRiesz fu
         (v,νv) = coRiesz fv
  preLeastSquareSolve m = plss
   where (mdu,mdv) = sepBlocks m
         mduLss = preLeastSquareSolve mdu
         mdvLss = preLeastSquareSolve mdv
         mdu0sp = nullSpaceProject mdu
         mdv0sp = nullSpaceProject mdv
         plss (u,v) = w₀ ^* ((u,v)^/^applyLinear m w₀)
          where w₀ = mdv0sp (mduLss u) ^+^ mdu0sp (mdvLss v)
  -- pseudoInverse m = RealVect $ coRiesz m

infixr 0 \$

(\$) :: (LeastSquares u, LeastSquares v, Scalar u ~ Scalar v)
          => LinearMap s u v -> v -> u
LinearMap m \$ v = leastSquareSolve m v
    
