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
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Math.LinearMap.TypeFamily.Class (LinearSpace (..)) where

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
  subtractLinearMaps CoOrigin CoOrigin = CoOrigin
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
  showsPrec p (LinearMap (RealVect n)) = showsPrec p n
instance ∀ u v . (Show (LinearMap ℝ u ℝ), Show (LinearMap ℝ v ℝ))
           => Show (LinearMap ℝ (u,v) ℝ) where
  showsPrec p (LinearMap (CoDirectSum m n))
        = showParen (p>6)
            (showsPrec 6 (LinearMap m :: LinearMap ℝ u ℝ)
                         . ("⊕"++) . showsPrec 7 (LinearMap n :: LinearMap ℝ v ℝ))
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
  subtractLinearMaps (RealVect v) (RealVect w) = RealVect $ v ^-^ w
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

#define FreeLinearSpace(V, LV)                          \
instance Num' s => LinearSpace (V s) where {             \
  newtype V s -→ w = LV (V w);                            \
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
FreeLinearSpace(V0, FromV0)
FreeLinearSpace(V1, FromV1)
FreeLinearSpace(V2, FromV2)
FreeLinearSpace(V3, FromV3)
FreeLinearSpace(V4, FromV4)
  
instance ∀ u v . (LinearSpace u, LinearSpace v, Scalar u ~ Scalar v)
                       => LinearSpace (u,v) where
  data (u,v) -→ w = CoDirectSum !(u-→w) !(v-→w)
  linearId = CoDirectSum linearCoFst linearCoSnd
  zeroMapping = CoDirectSum zeroMapping zeroMapping
  scaleLinearMap μ (CoDirectSum fu fv)
      = CoDirectSum (scaleLinearMap μ fu) (scaleLinearMap μ fv)
  addLinearMaps (CoDirectSum fu fv) (CoDirectSum fu' fv')
      = CoDirectSum (addLinearMaps fu fu') (addLinearMaps fv fv')
  subtractLinearMaps (CoDirectSum fu fv) (CoDirectSum fu' fv')
      = CoDirectSum (subtractLinearMaps fu fu') (subtractLinearMaps fv fv')
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

type DualSpace v = LinearMap (Scalar v) v (Scalar v)

type Fractional' s = (Fractional s, Eq s, VectorSpace s, Scalar s ~ s)

class (LinearSpace v, LinearSpace (Scalar v)) => SemiInner v where
  -- | Lazily enumerate choices of a basis of functionals that can be made dual
  --   to the given vectors, in order of preference (which roughly means, /large in
  --   the normal direction/. (I.e., if the vector @𝑣@ is assigned early to the
  --   dual vector @𝑣'@, then @𝑣' $ 𝑣$ should be large and all the other products
  --   comparably small. The purpose is that we should be able to make this basis
  --   orthonormal with a ~Gaussian-elimination approach, in a way that stays
  --   numerically stable. It is essentially the choice of a pivot element.)
  -- 
  --   For simple finite-dimensional array-vectors, you can easily define this
  --   method using 'cartesianDualBasisCandidates'.
  dualBasisCandidates :: [(Int,v)] -> Forest (Int, v -→ Scalar v)
--  coDualBasis :: [(i,DualSpace v)] -> [(i,v)]

cartesianDualBasisCandidates
     :: [v-→Scalar v]   -- ^ Set of canonical basis functionals.
     -> (v -> [ℝ])      -- ^ Decompose a vector in /absolute value/ components.
                        --   the list indices should correspond to those in
                        --   the functional list.
     -> ([(Int,v)] -> Forest (Int, v -→ Scalar v))
                        -- ^ Suitable definition of 'dualBasisCandidates'.
cartesianDualBasisCandidates dvs abss vcas = go 0 sorted
 where sorted = sortBy (comparing $ negate . snd . snd)
                       [ (i, (av, maximum av)) | (i,v)<-vcas, let av = abss v ]
       go k ((i,(av,_)):scs)
          | k<n   = Node (i, dv) (go (k+1) [(i',(zeroAt j av',m)) | (i',(av',m))<-scs])
                                : go k scs
          | otherwise = []
        where (j,_) = maximumBy (comparing snd) $ zip jfus av
              dv = dvs !! j
       
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
       candidates = map (second LinearMap) . sortBy (comparing fst) . findBest
                             $ dualBasisCandidates vsIxed
        where findBest [] = []
              findBest (Node iv' bv' : _) = iv' : findBest bv'
       vsIxed = zip [0..] vs

instance SemiInner ℝ where
  dualBasisCandidates = fmap ((`Node`[]) . second (RealVect . recip))
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

instance (Fractional' s, Ord s, SemiInner s) => SemiInner (V1 s) where
  dualBasisCandidates = fmap ((`Node`[]) . second (FromV1 . recip))
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

#define FreeSemiInner(V, LV, sabs) \
instance SemiInner (V) where {      \
  dualBasisCandidates                \
     = cartesianDualBasisCandidates (LV <$> Mat.basis) (fmap sabs . toList) }
FreeSemiInner(V2 ℝ, FromV2, abs)
FreeSemiInner(V3 ℝ, FromV3, abs)
FreeSemiInner(V4 ℝ, FromV4, abs)

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
  -- | For spaces with a canonical finite basis, this need not contain any
  --   information.
  data EntireBasis v :: *
  
  -- | Split up a linear map in “column vectors” WRT some suitable basis.
  decomposeLinMap :: (v-→w) -> (EntireBasis v, [w]->[w])
  
  recomposeEntire :: EntireBasis v -> [Scalar v] -> (v, [Scalar v])
  
  recomposeContraLinMap :: (LinearSpace w, Scalar w ~ Scalar v, Hask.Functor f)
           => (f (Scalar w) -> w) -> f (DualSpace v) -> v-→w
  
  sampleLinearFunction :: (v -> w) -> v-→w
  


instance (Num' s, LinearSpace s) => FiniteDimensional (ZeroDim s) where
  data EntireBasis (ZeroDim s) = ZeroBasis
  recomposeEntire ZeroBasis l = (Origin, l)
  decomposeLinMap _ = (ZeroBasis, id)
  recomposeContraLinMap _ _ = CoOrigin
  sampleLinearFunction _ = CoOrigin
  
instance (Num' s, LinearSpace s) => FiniteDimensional (V0 s) where
  data EntireBasis (V0 s) = V0Basis
  recomposeEntire V0Basis l = (V0, l)
  decomposeLinMap _ = (V0Basis, id)
  recomposeContraLinMap _ _ = FromV0 V0
  sampleLinearFunction _ = FromV0 V0
  
instance FiniteDimensional ℝ where
  data EntireBasis ℝ = RealsBasis
  recomposeEntire RealsBasis [] = (0, [])
  recomposeEntire RealsBasis (μ:cs) = (μ, cs)
  decomposeLinMap (RealVect v) = (RealsBasis, (v:))
  recomposeContraLinMap fw = RealVect . fw . fmap ($1)
  sampleLinearFunction f = RealVect $ f 1

#define FreeFiniteDimensional(V, VB, LV, take, give)      \
instance (Num' s, LinearSpace s)                           \
            => FiniteDimensional (V s) where {              \
  data EntireBasis (V s) = VB;                               \
  recomposeEntire _ (take:cs) = (give, cs);                   \
  recomposeEntire b cs = recomposeEntire b $ cs ++ [0];        \
  decomposeLinMap (LV m) = (VB, (toList m ++));                 \
  sampleLinearFunction f = LV $ fmap f Mat.identity;             \
  recomposeContraLinMap fw mv = LV $ (\v -> fw $ fmap ($v) mv) <$> Mat.identity }
FreeFiniteDimensional(V1, V1Basis, FromV1, c₀         , V1 c₀         )
FreeFiniteDimensional(V2, V2Basis, FromV2, c₀:c₁      , V2 c₀ c₁      )
FreeFiniteDimensional(V3, V3Basis, FromV3, c₀:c₁:c₂   , V3 c₀ c₁ c₂   )
FreeFiniteDimensional(V4, V4Basis, FromV4, c₀:c₁:c₂:c₃, V4 c₀ c₁ c₂ c₃)
                                  
deriving instance Show (EntireBasis ℝ)
  
instance ( FiniteDimensional u, InnerSpace u, FiniteDimensional v, InnerSpace v
         , Scalar u ~ Scalar v, Fractional' (Scalar v) )
            => FiniteDimensional (u,v) where
  data EntireBasis (u,v) = TupleBasis !(EntireBasis u) !(EntireBasis v)
  decomposeLinMap (CoDirectSum fu fv) = case (decomposeLinMap fu, decomposeLinMap fv) of
         ((bu, du), (bv, dv)) -> (TupleBasis bu bv, du . dv)
  recomposeEntire (TupleBasis bu bv) coefs = case recomposeEntire bu coefs of
                        (u, coefs') -> case recomposeEntire bv coefs' of
                         (v, coefs'') -> ((u,v), coefs'')
  recomposeContraLinMap fw dds
         = CoDirectSum (recomposeContraLinMap fw 
                         $ fmap (\(LinearMap (CoDirectSum v' _)) -> LinearMap v') dds)
                       (recomposeContraLinMap fw
                         $ fmap (\(LinearMap (CoDirectSum _ v')) -> LinearMap v') dds)
  sampleLinearFunction f = CoDirectSum (sampleLinearFunction $ f . (,zeroV))
                                       (sampleLinearFunction $ f . (zeroV,))
  
deriving instance (Show (EntireBasis u), Show (EntireBasis v))
                    => Show (EntireBasis (u,v))

infixr 0 \$

(\$) :: ( FiniteDimensional u, FiniteDimensional v, SemiInner v
        , Scalar u ~ Scalar v, Fractional (Scalar v) )
          => LinearMap s u v -> v -> u
(\$) (LinearMap m) = fst . \v -> recomposeEntire mbas [v' $ v | v' <- v's]
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m
    

pseudoInverse :: ( FiniteDimensional u, FiniteDimensional v, SemiInner v
        , Scalar u ~ Scalar v, Fractional (Scalar v) )
          => LinearMap s u v -> LinearMap s v u
pseudoInverse (LinearMap m) = LinearMap mi
 where mi = recomposeContraLinMap (fst . recomposeEntire mbas) v's
       v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m


riesz :: (FiniteDimensional v, InnerSpace v) => DualSpace v -> v
riesz (LinearMap dv) = fst . recomposeEntire bas $ compos []
 where (bas, compos) = decomposeLinMap dv

coRiesz :: (FiniteDimensional v, InnerSpace v) => v -> DualSpace v
coRiesz v = LinearMap $ sampleLinearFunction (v<.>)

showsPrecAsRiesz :: (FiniteDimensional v, InnerSpace v, Show v)
                      => Int -> DualSpace v -> ShowS
showsPrecAsRiesz p dv = showParen (p>9) $ ("coRiesz "++) . showsPrec 10 (riesz dv)

instance Show (LinearMap ℝ (V0 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V1 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V2 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V3 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V4 ℝ) ℝ) where showsPrec = showsPrecAsRiesz


infixl 7 ×<
(×<) :: (FiniteDimensional v, InnerSpace v, HasBasis w, Scalar v ~ Scalar w)
           => Basis w -> v -> LinearMap (Scalar v) v w
bw ×< v = LinearMap $ sampleLinearFunction (\v' -> recompose [(bw, v<.>v')])

instance Show (LinearMap s v (V0 s)) where
  show _ = "zeroV"
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V1 ℝ)) where
  showsPrec p m = showParen (p>6) $ ("ex ×< "++) . showsPrec 7 (riesz $ coRiesz (V1 1) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V2 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex×<"++) . showsPrec 7 (riesz $ coRiesz (V2 1 0) . m)
         . (" ^+^ ey×<"++) . showsPrec 7 (riesz $ coRiesz (V2 0 1) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V3 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex×<"++) . showsPrec 7 (riesz $ coRiesz (V3 1 0 0) . m)
         . (" ^+^ ey×<"++) . showsPrec 7 (riesz $ coRiesz (V3 0 1 0) . m)
         . (" ^+^ ez×<"++) . showsPrec 7 (riesz $ coRiesz (V3 0 0 1) . m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V4 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex×<"++) . showsPrec 7 (riesz $ coRiesz (V4 1 0 0 0) . m)
         . (" ^+^ ey×<"++) . showsPrec 7 (riesz $ coRiesz (V4 0 1 0 0) . m)
         . (" ^+^ ez×<"++) . showsPrec 7 (riesz $ coRiesz (V4 0 0 1 0) . m)
         . (" ^+^ ew×<"++) . showsPrec 7 (riesz $ coRiesz (V4 0 0 0 1) . m)

