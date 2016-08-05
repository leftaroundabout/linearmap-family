-- |
-- Module      : Math.LinearMap.Category
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
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Math.LinearMap.Category (
            -- * Linear maps
              LinearMap (..), (+>)()
            , DualSpace
            , (⊕), (>+<)
            -- * Solving linear equations
            , (\$), pseudoInverse
            -- * The classes of suitable vector spaces
            -- ** General linear maps
            , LinearSpace (..)
            -- ** Orthonormal systems
            , SemiInner (..), cartesianDualBasisCandidates
            -- ** Finite baseis
            , FiniteDimensional (..)
            -- * Utility
            , riesz, coRiesz, showsPrecAsRiesz, (.<)
            , Num', Fractional'
            ) where

import Data.VectorSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.Tree (Tree(..), Forest)
import Data.List (sortBy, foldl')
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Ord (comparing)
import Data.List (maximumBy)
import Data.Foldable (toList)

import Data.VectorSpace.Free
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat

type Num' s = (Num s, VectorSpace s, Scalar s ~ s)

-- | The class of vector spaces which implement linear maps. Alternatively,
--   this can be considered as the class of spaces with a properly tractable
--   <https://en.wikipedia.org/wiki/Dual_space dual space>.
class (VectorSpace v, Num' (Scalar v)) => LinearSpace v where
  -- | Internal representation of a linear map from the space @v@ to the space @w@.
  --   For array-of-numbers Hilbert spaces, this will generally be just
  --   an “array of column vectors”, or, in the special case 'w ~ Scalar v',
  --   a single vector that's considered as a “row vector”. (More precisely
  --   speaking, this represents a /dual vector/: a member of the 'DualSpace',
  --   aka a <https://en.wikipedia.org/wiki/Linear_form functional>.)
  -- 
  --   Only use the '-→' type and the methods below for /instantiating/ this class.
  --   For actually /working/ with linear mappings, use the 'LinearMap' wrapper.
  type LinearMapping v w :: *
 
  linearId :: v +> v
  zeroMapping :: (LinearSpace w, Scalar w ~ Scalar v) => v +> w
  addLinearMaps :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v +> w) -> (v +> w) -> v +> w
  subtractLinearMaps :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v +> w) -> (v +> w) -> v +> w
  subtractLinearMaps m n = addLinearMaps m (negateLinearMap n)
  scaleLinearMap :: (LinearSpace w, Scalar w ~ Scalar v)
                => Scalar v -> (v +> w) -> v +> w
  negateLinearMap :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v +> w) -> v +> w
  linearCoFst :: (LinearSpace w, Scalar w ~ Scalar v)
                => v +> (v,w)
  linearCoSnd :: (LinearSpace w, Scalar w ~ Scalar v)
                => v +> (w,v)
  fanoutBlocks :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>w) -> (v+>x) -> v +> (w,x)
  fstBlock :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>(w,x)) -> v +> w
  sndBlock :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>(w,x)) -> v +> x
  sepBlocks :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>(w,x)) -> (v+>w, v+>x)
  sepBlocks m = (fstBlock m, sndBlock m)
  firstBlock :: ( LinearSpace w, LinearSpace x
                , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
     => (v+>w) -> v +> (w,x)
  secondBlock :: ( LinearSpace w, LinearSpace x
                      , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => (v+>x) -> v +> (w,x)
  applyLinear :: (LinearSpace w, Scalar w ~ Scalar v)
                => (v +> w) -> v -> w
  composeLinear :: ( LinearSpace w, LinearSpace x
                   , Scalar w ~ Scalar v, Scalar x ~ Scalar v )
           => (w +> x) -> (v +> w) -> v +> x



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
  type LinearMapping (ZeroDim s) v = ZeroDim s
  linearId = LinearMap Origin
  zeroMapping = LinearMap Origin
  negateLinearMap (LinearMap Origin) = LinearMap Origin
  scaleLinearMap _ (LinearMap Origin) = LinearMap Origin
  addLinearMaps (LinearMap Origin) (LinearMap Origin) = LinearMap Origin
  subtractLinearMaps (LinearMap Origin) (LinearMap Origin) = LinearMap Origin
  linearCoFst = LinearMap Origin
  linearCoSnd = LinearMap Origin
  fstBlock (LinearMap Origin) = LinearMap Origin
  sndBlock (LinearMap Origin) = LinearMap Origin
  fanoutBlocks (LinearMap Origin) (LinearMap Origin) = LinearMap Origin
  firstBlock (LinearMap Origin) = LinearMap Origin
  secondBlock (LinearMap Origin) = LinearMap Origin
  applyLinear _ _ = zeroV
  composeLinear _ _ = LinearMap Origin


-- | The cartesian monoidal category of vector spaces over the field @s@
--   with linear maps as morphisms. This category is in maths called
--   <https://en.wikipedia.org/wiki/Category_of_modules#Example:_the_category_of_vector_spaces VectK>.
-- 
--   The common matrix operations are given by:
-- 
--   * Identity matrix: 'Control.Category.Constrained.id'.
--   * Matrix addition: 'Data.AdditiveGroup.^+^' (linear maps form an ordinary vector space).
--   * Matrix-matrix multiplication: 'Control.Category.Constrained..'.
--   * Matrix-vector multiplication: 'Control.Arrow.Constrained.$'.
--   * Vertical matrix concatenation: 'Control.Arrow.Constrained.&&&'.
--   * Horizontal matrix concatenation: '⊕', aka '>+<'.
newtype LinearMap s v w = LinearMap {getLinearMap :: LinearMapping v w}

-- | Infix synonym for 'LinearMap', without explicit mention of the scalar type.
type v +> w = LinearMap (Scalar v) v w

instance (LinearSpace v, LinearSpace w, Scalar v~s, Scalar w~s)
               => AdditiveGroup (LinearMap s v w) where
  zeroV = zeroMapping
  (^+^) = addLinearMaps
  (^-^) = subtractLinearMaps
  negateV = negateLinearMap
instance (LinearSpace v, LinearSpace w, Scalar v~s, Scalar w~s)
               => VectorSpace (LinearMap s v w) where
  type Scalar (LinearMap s v w) = s
  (*^) = scaleLinearMap
instance Num (LinearMap ℝ ℝ ℝ) where
  fromInteger = LinearMap . fromInteger
  (+) = (^+^)
  (-) = (^-^)
  LinearMap m * LinearMap n
         = LinearMap $ m*n
  abs (LinearMap n) = LinearMap $ abs n
  signum (LinearMap n) = LinearMap $ signum n
instance Fractional (LinearMap ℝ ℝ ℝ) where
  fromRational = LinearMap . fromRational
  LinearMap m / LinearMap n
         = LinearMap $ m/n
  recip (LinearMap n) = LinearMap $ recip n
  
infixr 6 ⊕, >+<

-- | The dual operation to the tuple constructor, or rather to the
--   '&&&' fanout operation: evaluate two (linear) functions in parallel
--   and sum up the results.
--   The typical use is to concatenate “row vectors” in a matrix definition.
(⊕) :: (u+>w) -> (v+>w) -> (u,v)+>w
LinearMap m ⊕ LinearMap n = LinearMap $ (m, n)

-- | ASCII version of '⊕'
(>+<) :: (u+>w) -> (v+>w) -> (u,v)+>w
(>+<) = (⊕)

pattern (:⊕) :: LinearMap s u w -> LinearMap s v w -> LinearMap s (u,v) w
pattern (:⊕) m n <- LinearMap (LinearMap -> m, LinearMap -> n)
 where LinearMap m :⊕ LinearMap n = LinearMap (m,n)

instance Show (LinearMap ℝ ℝ ℝ) where
  showsPrec p (LinearMap n) = showsPrec p n
instance ∀ u v . (Show (LinearMap ℝ u ℝ), Show (LinearMap ℝ v ℝ))
           => Show (LinearMap ℝ (u,v) ℝ) where
  showsPrec p (LinearMap ((m, n)))
        = showParen (p>6)
            (showsPrec 6 (LinearMap m :: LinearMap ℝ u ℝ)
                         . ("⊕"++) . showsPrec 7 (LinearMap n :: LinearMap ℝ v ℝ))
instance ∀ s u v w . ( LinearSpace u, LinearSpace v, LinearSpace w
                     , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
                     , Show (LinearMap s u v), Show (LinearMap s u w) )
           => Show (LinearMap s u (v,w)) where
  showsPrec p m
        = showParen (p>6)
            (showsPrec 6 mv . (" &&& "++) . showsPrec 6 mw)
   where (mv, mw) = sepBlocks m

instance Category (LinearMap s) where
  type Object (LinearMap s) v = (LinearSpace v, Scalar v ~ s)
  id = linearId
  (.) = composeLinear
instance Num' s => Cartesian (LinearMap s) where
  type UnitObject (LinearMap s) = ZeroDim s
  swap = linearCoSnd ⊕ linearCoFst
  attachUnit = linearCoFst
  detachUnit = fst
  regroup = linearCoFst . linearCoFst ⊕ (linearCoFst . linearCoSnd ⊕ linearCoSnd)
  regroup' = (linearCoFst ⊕ linearCoSnd . linearCoFst) ⊕ linearCoSnd . linearCoSnd
instance Num' s => Morphism (LinearMap s) where
  f *** g = firstBlock f ⊕ secondBlock g
instance Num' s => PreArrow (LinearMap s) where
  (&&&) = fanoutBlocks
  terminal = zeroV
  fst = lfstBlock id
  snd = lsndBlock id
instance Num' s => EnhancedCat (->) (LinearMap s) where
  arr m = applyLinear m

type ℝ = Double

instance LinearSpace ℝ where
  type LinearMapping ℝ w = w
  linearId = LinearMap 1
  zeroMapping = LinearMap zeroV
  scaleLinearMap μ (LinearMap v) = LinearMap $ μ *^ v
  addLinearMaps (LinearMap v) (LinearMap w) = LinearMap $ v ^+^ w
  subtractLinearMaps (LinearMap v) (LinearMap w) = LinearMap $ v ^-^ w
  negateLinearMap (LinearMap w) = LinearMap $ negateV w
  linearCoFst = LinearMap (1, zeroV)
  linearCoSnd = LinearMap (zeroV, 1)
  fstBlock (LinearMap (u, v)) = LinearMap u
  sndBlock (LinearMap (u, v)) = LinearMap v
  fanoutBlocks (LinearMap v) (LinearMap w) = LinearMap (v,w)
  firstBlock (LinearMap v) = LinearMap (v,zeroV)
  secondBlock (LinearMap w) = LinearMap (zeroV,w)
  applyLinear (LinearMap w) μ = μ *^ w
  composeLinear f (LinearMap w) = LinearMap $ applyLinear f w

#define FreeLinearSpace(V, LV)                          \
instance Num' s => LinearSpace (V s) where {             \
  type LinearMapping (V s) w = V w;                       \
  linearId = LV Mat.identity;                              \
  zeroMapping = LV $ pure zeroV;                            \
  addLinearMaps (LV m) (LV n) = LV $ liftA2 (^+^) m n;       \
  subtractLinearMaps (LV m) (LV n) = LV $ liftA2 (^-^) m n;   \
  negateLinearMap (LV m) = LV $ fmap negateV m;                \
  scaleLinearMap μ (LV m) = LV $ fmap (μ*^) m;                  \
  linearCoFst = LV $ fmap (,zeroV) Mat.identity;                 \
  linearCoSnd = LV $ fmap (zeroV,) Mat.identity;                  \
  fstBlock (LV m) = LV $ fmap fst m;                               \
  sndBlock (LV m) = LV $ fmap snd m;                                \
  fanoutBlocks (LV m) (LV n) = LV $ liftA2 (,) m n;                  \
  firstBlock (LV m) = LV $ fmap (,zeroV) m;                           \
  secondBlock (LV m) = LV $ fmap (zeroV,) m;                           \
  applyLinear (LV m) v = foldl' (^+^) zeroV $ liftA2 (^*) m v;          \
  composeLinear f (LV m) = LV $ fmap (applyLinear f) m }
FreeLinearSpace(V0, LinearMap)
FreeLinearSpace(V1, LinearMap)
FreeLinearSpace(V2, LinearMap)
FreeLinearSpace(V3, LinearMap)
FreeLinearSpace(V4, LinearMap)
  
instance ∀ u v . (LinearSpace u, LinearSpace v, Scalar u ~ Scalar v)
                       => LinearSpace (u,v) where
  type LinearMapping (u,v) w = (LinearMapping u w, LinearMapping v w)
  linearId = linearCoFst ⊕ linearCoSnd
  zeroMapping = zeroMapping ⊕ zeroMapping
  scaleLinearMap μ (LinearMap (fu, fv))
              = μ *^ LinearMap fu ⊕ μ *^ LinearMap fv
  addLinearMaps (LinearMap (fu, fv)) (LinearMap (fu', fv'))
          = (LinearMap fu ^+^ LinearMap fu') ⊕ (LinearMap fv ^+^ LinearMap fv')
  subtractLinearMaps (LinearMap (fu, fv)) (LinearMap (fu', fv'))
          = (LinearMap fu ^-^ LinearMap fu') ⊕ (LinearMap fv ^-^ LinearMap fv')
  negateLinearMap (LinearMap (fu, fv)) = negateV (LinearMap fu) ⊕ negateV (LinearMap fv)
  linearCoFst = composeLinear linearCoFst linearCoFst ⊕ composeLinear linearCoFst linearCoSnd
  linearCoSnd = composeLinear linearCoSnd linearCoFst ⊕ composeLinear linearCoSnd linearCoSnd
  fstBlock (fu :⊕ fv) = fstBlock fu ⊕ fstBlock fv
  sndBlock (fu :⊕ fv) = sndBlock fu ⊕ sndBlock fv
  sepBlocks (LinearMap (fu, fv)) = (fuw ⊕ fvw, fux ⊕ fvx)
   where (fuw,fux) = sepBlocks $ LinearMap fu
         (fvw,fvx) = sepBlocks $ LinearMap fv
  fanoutBlocks (LinearMap (fu, fv)) (LinearMap (gu, gv))
              = fanoutBlocks (LinearMap fu) (LinearMap gu)
                ⊕ fanoutBlocks (LinearMap fv) (LinearMap gv)
  firstBlock (LinearMap (fu, fv)) = firstBlock (LinearMap fu) ⊕ firstBlock (LinearMap fv)
  secondBlock (LinearMap (fu, fv)) = secondBlock (LinearMap fu) ⊕ secondBlock (LinearMap fv)
  applyLinear (LinearMap (fu, fv)) (u,v)
             = applyLinear (LinearMap fu) u ^+^ applyLinear (LinearMap fv) v
  composeLinear f (LinearMap (fu, fv))
        = composeLinear f (LinearMap fu) ⊕ composeLinear f (LinearMap fv)

lfstBlock :: ( LinearSpace u, LinearSpace v, LinearSpace w
             , Scalar u ~ Scalar v, Scalar v ~ Scalar w )
          => (u+>w) -> (u,v)+>w
lfstBlock f = f ⊕ zeroMapping
lsndBlock :: ( LinearSpace u, LinearSpace v, LinearSpace w
            , Scalar u ~ Scalar v, Scalar v ~ Scalar w )
          => (v+>w) -> (u,v)+>w
lsndBlock f = zeroMapping ⊕ f

type DualSpace v = v+>Scalar v

type Fractional' s = (Fractional s, Eq s, VectorSpace s, Scalar s ~ s)

-- | 'SemiInner' is the class of vector spaces with finite subspaces in which
--   you can define a basis that can be used to project from the whole space
--   into the subspace. The usual application is for using a kind of
--   <https://en.wikipedia.org/wiki/Galerkin_method Galerkin method> to
--   give an approximate solution (see '\$') to a linear equation in a possibly
--   infinite-dimensional space.
-- 
--   Of course, this also works for spaces which are already finite-dimensional themselves.
class (LinearSpace v, LinearSpace (Scalar v)) => SemiInner v where
  -- | Lazily enumerate choices of a basis of functionals that can be made dual
  --   to the given vectors, in order of preference (which roughly means, large in
  --   the normal direction.) I.e., if the vector @𝑣@ is assigned early to the
  --   dual vector @𝑣'@, then @(𝑣' $ 𝑣)@ should be large and all the other products
  --   comparably small.
  -- 
  --   The purpose is that we should be able to make this basis orthonormal
  --   with a ~Gaussian-elimination approach, in a way that stays numerically
  --   stable. This is otherwise known as the /choice of a pivot element/.
  -- 
  --   For simple finite-dimensional array-vectors, you can easily define this
  --   method using 'cartesianDualBasisCandidates'.
  dualBasisCandidates :: [(Int,v)] -> Forest (Int, v +> Scalar v)

cartesianDualBasisCandidates
     :: [v+>Scalar v]   -- ^ Set of canonical basis functionals.
     -> (v -> [ℝ])      -- ^ Decompose a vector in /absolute value/ components.
                        --   the list indices should correspond to those in
                        --   the functional list.
     -> ([(Int,v)] -> Forest (Int, v +> Scalar v))
                        -- ^ Suitable definition of 'dualBasisCandidates'.
cartesianDualBasisCandidates dvs abss vcas = go 0 sorted
 where sorted = sortBy (comparing $ negate . snd . snd)
                       [ (i, (av, maximum av)) | (i,v)<-vcas, let av = abss v ]
       go k ((i,(av,_)):scs)
          | k<n   = Node (i, dv) (go (k+1) [(i',(zeroAt j av',m)) | (i',(av',m))<-scs])
                                : go k scs
        where (j,_) = maximumBy (comparing snd) $ zip jfus av
              dv = dvs !! j
       go _ _ = []
       
       jfus = [0 .. n-1]
       n = length dvs
       
       zeroAt :: Int -> [ℝ] -> [ℝ]
       zeroAt _ [] = []
       zeroAt 0 (_:l) = (-1/0):l
       zeroAt j (e:l) = e : zeroAt (j-1) l

instance (Fractional' s, SemiInner s) => SemiInner (ZeroDim s) where
  dualBasisCandidates _ = []
instance (Fractional' s, SemiInner s) => SemiInner (V0 s) where
  dualBasisCandidates _ = []

orthonormaliseDuals :: (SemiInner v, Fractional (Scalar v))
                          => [(v, DualSpace v)] -> [(v,DualSpace v)]
orthonormaliseDuals [] = []
orthonormaliseDuals ((v,v'₀):ws) = (v,v') : [(w, w' ^-^ (w'$v)*^v') | (w,w')<-wssys]
 where wssys = orthonormaliseDuals ws
       v'₁ = foldl' (\v'i (w,w') -> v'i ^-^ (v'i$w)*^w') v'₀ wssys
       v' = v'₁ ^/ (v'₁$v)

dualBasis :: (SemiInner v, Fractional (Scalar v)) => [v] -> [DualSpace v]
dualBasis vs = snd <$> orthonormaliseDuals (zip' vsIxed candidates)
 where zip' ((i,v):vs) ((j,v'):ds)
        | i<j   = zip' vs ((j,v'):ds)
        | i==j  = (v,v') : zip' vs ds
       zip' _ _ = []
       candidates = sortBy (comparing fst) . findBest
                             $ dualBasisCandidates vsIxed
        where findBest [] = []
              findBest (Node iv' bv' : _) = iv' : findBest bv'
       vsIxed = zip [0..] vs

instance SemiInner ℝ where
  dualBasisCandidates = fmap ((`Node`[]) . second (LinearMap . recip))
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

instance (Fractional' s, Ord s, SemiInner s) => SemiInner (V1 s) where
  dualBasisCandidates = fmap ((`Node`[]) . second (LinearMap . recip))
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

#define FreeSemiInner(V, sabs) \
instance SemiInner (V) where {      \
  dualBasisCandidates                \
     = cartesianDualBasisCandidates (LinearMap <$> Mat.basis) (fmap sabs . toList) }
FreeSemiInner(V2 ℝ, abs)
FreeSemiInner(V3 ℝ, abs)
FreeSemiInner(V4 ℝ, abs)

instance (SemiInner u, SemiInner v, Scalar u ~ Scalar v) => SemiInner (u,v) where
  dualBasisCandidates = fmap (\(i,(u,v))->((i,u),(i,v))) >>> unzip
              >>> dualBasisCandidates *** dualBasisCandidates
              >>> combineBaseis False mempty
   where combineBaseis _ _ ([], []) = []
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
         combineBaseis _ forbidden (bu, []) = combineBaseis False forbidden (bu,[])
         combineBaseis _ forbidden ([], bv) = combineBaseis True forbidden ([],bv)
  
(^/^) :: (InnerSpace v, Eq (Scalar v), Fractional (Scalar v)) => v -> v -> Scalar v
v^/^w = case (v<.>w) of
   0 -> 0
   vw -> vw / (w<.>w)

class (LinearSpace v, LinearSpace (Scalar v)) => FiniteDimensional v where
  -- | Whereas 'Basis'-values refer to a single basis vector, a single
  --   'EntireBasis' value represents a complete collection of such basis vectors,
  --   which can be used to associate a vector with a list of coefficients.
  -- 
  --   For spaces with a canonical finite basis, 'EntireBasis' does not actually
  --   need to contain any information, since all vectors will anyway be represented in
  --   that same basis.
  data EntireBasis v :: *
  
  -- | Split up a linear map in “column vectors” WRT some suitable basis.
  decomposeLinMap :: (v+>w) -> (EntireBasis v, [w]->[w])
  
  recomposeEntire :: EntireBasis v -> [Scalar v] -> (v, [Scalar v])
  
  recomposeContraLinMap :: (LinearSpace w, Scalar w ~ Scalar v, Hask.Functor f)
           => (f (Scalar w) -> w) -> f (DualSpace v) -> v+>w
  
  sampleLinearFunction :: (v -> w) -> v+>w
  


instance (Num' s, LinearSpace s) => FiniteDimensional (ZeroDim s) where
  data EntireBasis (ZeroDim s) = ZeroBasis
  recomposeEntire ZeroBasis l = (Origin, l)
  decomposeLinMap _ = (ZeroBasis, id)
  recomposeContraLinMap _ _ = LinearMap Origin
  sampleLinearFunction _ = LinearMap Origin
  
instance (Num' s, LinearSpace s) => FiniteDimensional (V0 s) where
  data EntireBasis (V0 s) = V0Basis
  recomposeEntire V0Basis l = (V0, l)
  decomposeLinMap _ = (V0Basis, id)
  recomposeContraLinMap _ _ = LinearMap V0
  sampleLinearFunction _ = LinearMap V0
  
instance FiniteDimensional ℝ where
  data EntireBasis ℝ = RealsBasis
  recomposeEntire RealsBasis [] = (0, [])
  recomposeEntire RealsBasis (μ:cs) = (μ, cs)
  decomposeLinMap (LinearMap v) = (RealsBasis, (v:))
  recomposeContraLinMap fw = LinearMap . fw . fmap ($1)
  sampleLinearFunction f = LinearMap $ f 1

#define FreeFiniteDimensional(V, VB, take, give)          \
instance (Num' s, LinearSpace s)                           \
            => FiniteDimensional (V s) where {              \
  data EntireBasis (V s) = VB;                               \
  recomposeEntire _ (take:cs) = (give, cs);                   \
  recomposeEntire b cs = recomposeEntire b $ cs ++ [0];        \
  decomposeLinMap (LinearMap m) = (VB, (toList m ++));          \
  sampleLinearFunction f = LinearMap $ fmap f Mat.identity;      \
  recomposeContraLinMap fw mv = LinearMap $ (\v -> fw $ fmap ($v) mv) <$> Mat.identity }
FreeFiniteDimensional(V1, V1Basis, c₀         , V1 c₀         )
FreeFiniteDimensional(V2, V2Basis, c₀:c₁      , V2 c₀ c₁      )
FreeFiniteDimensional(V3, V3Basis, c₀:c₁:c₂   , V3 c₀ c₁ c₂   )
FreeFiniteDimensional(V4, V4Basis, c₀:c₁:c₂:c₃, V4 c₀ c₁ c₂ c₃)
                                  
deriving instance Show (EntireBasis ℝ)
  
instance ( FiniteDimensional u, InnerSpace u, FiniteDimensional v, InnerSpace v
         , Scalar u ~ Scalar v, Fractional' (Scalar v) )
            => FiniteDimensional (u,v) where
  data EntireBasis (u,v) = TupleBasis !(EntireBasis u) !(EntireBasis v)
  decomposeLinMap (LinearMap (fu, fv))
       = case (decomposeLinMap (LinearMap fu), decomposeLinMap (LinearMap fv)) of
         ((bu, du), (bv, dv)) -> (TupleBasis bu bv, du . dv)
  recomposeEntire (TupleBasis bu bv) coefs = case recomposeEntire bu coefs of
                        (u, coefs') -> case recomposeEntire bv coefs' of
                         (v, coefs'') -> ((u,v), coefs'')
  recomposeContraLinMap fw dds
         = recomposeContraLinMap fw 
               (fmap (\(LinearMap (v', _)) -> LinearMap v') dds)
          ⊕ recomposeContraLinMap fw
               (fmap (\(LinearMap (_, v')) -> LinearMap v') dds)
  sampleLinearFunction f = sampleLinearFunction (f . (,zeroV))
                         ⊕ sampleLinearFunction (f . (zeroV,))
  
deriving instance (Show (EntireBasis u), Show (EntireBasis v))
                    => Show (EntireBasis (u,v))

infixr 0 \$

-- | Inverse function application, in the sense of providing a
--   /least-squares-error/ solution to a linear equation system.
-- 
--   If you want to solve for multiple RHS vectors, be sure to partially
--   apply this operator to the matrix element.
(\$) :: ( FiniteDimensional u, FiniteDimensional v, SemiInner v
        , Scalar u ~ Scalar v, Fractional (Scalar v) )
          => (u+>v) -> v -> u
(\$) m = fst . \v -> recomposeEntire mbas [v' $ v | v' <- v's]
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m
    

pseudoInverse :: ( FiniteDimensional u, FiniteDimensional v, SemiInner v
        , Scalar u ~ Scalar v, Fractional (Scalar v) )
          => (u+>v) -> v+>u
pseudoInverse m = recomposeContraLinMap (fst . recomposeEntire mbas) v's
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m


-- | The <https://en.wikipedia.org/wiki/Riesz_representation_theorem Riesz representation theorem>
--   provides an isomorphism between a Hilbert space and its (continuous) dual space.
riesz :: (FiniteDimensional v, InnerSpace v) => DualSpace v -> v
riesz dv = fst . recomposeEntire bas $ compos []
 where (bas, compos) = decomposeLinMap dv

coRiesz :: (FiniteDimensional v, InnerSpace v) => v -> DualSpace v
coRiesz v = sampleLinearFunction (v<.>)

-- | Functions are generally a pain to display, but since linear functionals
--   in a Hilbert space can be represented by /vectors/ in that space,
--   this can be used for implementing a 'Show' instance.
showsPrecAsRiesz :: (FiniteDimensional v, InnerSpace v, Show v)
                      => Int -> DualSpace v -> ShowS
showsPrecAsRiesz p dv = showParen (p>9) $ ("coRiesz "++) . showsPrec 10 (riesz dv)

instance Show (LinearMap ℝ (V0 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V1 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V2 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V3 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V4 ℝ) ℝ) where showsPrec = showsPrecAsRiesz


infixl 7 .<

-- | Outer product of a general @v@-vector and a basis element from @w@.
--   Note that this operation is in general pretty inefficient; it is
--   provided mostly to lay out matrix definitions neatly.
(.<) :: (FiniteDimensional v, InnerSpace v, HasBasis w, Scalar v ~ Scalar w)
           => Basis w -> v -> v+>w
bw .< v = sampleLinearFunction (\v' -> recompose [(bw, v<.>v')])

instance Show (LinearMap s v (V0 s)) where
  show _ = "zeroV"
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V1 ℝ)) where
  showsPrec p m = showParen (p>6) $ ("ex ×< "++) . showsPrec 7 (riesz $ coRiesz (V1 1) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V2 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (riesz $ coRiesz (V2 1 0) . m)
         . (" ^+^ ey.<"++) . showsPrec 7 (riesz $ coRiesz (V2 0 1) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V3 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (riesz $ coRiesz (V3 1 0 0) . m)
         . (" ^+^ ey.<"++) . showsPrec 7 (riesz $ coRiesz (V3 0 1 0) . m)
         . (" ^+^ ez.<"++) . showsPrec 7 (riesz $ coRiesz (V3 0 0 1) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V4 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (riesz $ coRiesz (V4 1 0 0 0) . m)
         . (" ^+^ ey.<"++) . showsPrec 7 (riesz $ coRiesz (V4 0 1 0 0) . m)
         . (" ^+^ ez.<"++) . showsPrec 7 (riesz $ coRiesz (V4 0 0 1 0) . m)
         . (" ^+^ ew.<"++) . showsPrec 7 (riesz $ coRiesz (V4 0 0 0 1) . m)

