-- |
-- Module      : Math.LinearMap.Category
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE CPP                  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnicodeSyntax        #-}

module Math.LinearMap.Category (
            -- * Linear maps
            -- ** Tensor implementation
              LinearMap (..), (+>)()
            , (⊕), (>+<)
            -- ** Function implementation
            , LinearFunction (..), (-+>)(), Bilinear
            -- ** Hermitian
            , Metric, euclideanMetric
            -- * Solving linear equations
            , (\$), pseudoInverse
            -- * Eigenvalue problems
            , Eigenvector(..), constructEigenSystem
            -- * The classes of suitable vector spaces
            -- ** Tensor products
            , TensorSpace
            -- ** Functionals linear maps
            , LinearSpace (..)
            -- ** Orthonormal systems
            , SemiInner (..), cartesianDualBasisCandidates
            -- ** Finite baseis
            , FiniteDimensional (..)
            -- * Utility
            -- ** Linear primitives
            , addV, scale, inner, flipBilin, bilinearFunction
            -- ** Hilbert space operations
            , DualSpace, riesz, coRiesz, showsPrecAsRiesz, (.<)
            -- ** Constraints on types of scalars
            , Num', Num'', Num''', Fractional', Fractional''
            ) where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted

import Data.Tree (Tree(..), Forest)
import Data.List (sortBy, foldl')
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Ord (comparing)
import Data.List (maximumBy)
import Data.Foldable (toList)

import Data.VectorSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.VectorSpace.Free
import Math.VectorSpace.ZeroDimensional
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import Control.Lens ((^.))



-- | 'SemiInner' is the class of vector spaces with finite subspaces in which
--   you can define a basis that can be used to project from the whole space
--   into the subspace. The usual application is for using a kind of
--   <https://en.wikipedia.org/wiki/Galerkin_method Galerkin method> to
--   give an approximate solution (see '\$') to a linear equation in a possibly
--   infinite-dimensional space.
-- 
--   Of course, this also works for spaces which are already finite-dimensional themselves.
class LSpace v => SemiInner v where
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
  dualBasisCandidates :: [(Int,v)] -> Forest (Int, DualVector v)

cartesianDualBasisCandidates
     :: [DualVector v]  -- ^ Set of canonical basis functionals.
     -> (v -> [ℝ])      -- ^ Decompose a vector in /absolute value/ components.
                        --   the list indices should correspond to those in
                        --   the functional list.
     -> ([(Int,v)] -> Forest (Int, DualVector v))
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

instance (Fractional'' s, SemiInner s) => SemiInner (ZeroDim s) where
  dualBasisCandidates _ = []
instance (Fractional'' s, SemiInner s) => SemiInner (V0 s) where
  dualBasisCandidates _ = []

(<.>^) :: LSpace v => DualVector v -> v -> Scalar v
f<.>^v = (applyDualVector$f)$v

orthonormaliseDuals :: (SemiInner v, LSpace v, Fractional'' (Scalar v))
                          => [(v, DualVector v)] -> [(v,DualVector v)]
orthonormaliseDuals [] = []
orthonormaliseDuals ((v,v'₀):ws)
          = (v,v') : [(w, w' ^-^ (w'<.>^v)*^v') | (w,w')<-wssys]
 where wssys = orthonormaliseDuals ws
       v'₁ = foldl' (\v'i (w,w') -> v'i ^-^ (v'i<.>^w)*^w') v'₀ wssys
       v' = v'₁ ^/ (v'₁<.>^v)

dualBasis :: (SemiInner v, LSpace v, Fractional'' (Scalar v)) => [v] -> [DualVector v]
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
  dualBasisCandidates = fmap ((`Node`[]) . second recip)
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

instance (Fractional'' s, Ord s, SemiInner s) => SemiInner (V1 s) where
  dualBasisCandidates = fmap ((`Node`[]) . second recip)
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

#define FreeSemiInner(V, sabs) \
instance SemiInner (V) where {  \
  dualBasisCandidates            \
     = cartesianDualBasisCandidates Mat.basis (fmap sabs . toList) }
FreeSemiInner(V2 ℝ, abs)
FreeSemiInner(V3 ℝ, abs)
FreeSemiInner(V4 ℝ, abs)

instance ∀ u v . ( SemiInner u, SemiInner v, Scalar u ~ Scalar v ) => SemiInner (u,v) where
  dualBasisCandidates = fmap (\(i,(u,v))->((i,u),(i,v))) >>> unzip
              >>> dualBasisCandidates *** dualBasisCandidates
              >>> combineBaseis False mempty
   where combineBaseis :: Bool -> Set Int
                 -> ( Forest (Int, DualVector u)
                    , Forest (Int, DualVector v) )
                   -> Forest (Int, (DualVector u, DualVector v))
         combineBaseis _ _ ([], []) = []
         combineBaseis False forbidden (Node (i,du) bu' : abu, bv)
            | i`Set.member`forbidden  = combineBaseis False forbidden (abu, bv)
            | otherwise
                 = Node (i, (du, zeroV))
                        (combineBaseis True (Set.insert i forbidden) (bu', bv))
                       : combineBaseis False forbidden (abu, bv)
         combineBaseis True forbidden (bu, Node (i,dv) bv' : abv)
            | i`Set.member`forbidden  = combineBaseis True forbidden (bu, abv)
            | otherwise
                 = Node (i, (zeroV, dv))
                        (combineBaseis False (Set.insert i forbidden) (bu, bv'))
                       : combineBaseis True forbidden (bu, abv)
         combineBaseis _ forbidden (bu, []) = combineBaseis False forbidden (bu,[])
         combineBaseis _ forbidden ([], bv) = combineBaseis True forbidden ([],bv)
  
(^/^) :: (InnerSpace v, Eq (Scalar v), Fractional (Scalar v)) => v -> v -> Scalar v
v^/^w = case (v<.>w) of
   0 -> 0
   vw -> vw / (w<.>w)

class (LSpace v, LSpace (Scalar v)) => FiniteDimensional v where
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
           => (f (Scalar w) -> w) -> f (DualVector v) -> v+>w
  


instance (Num''' s) => FiniteDimensional (ZeroDim s) where
  data EntireBasis (ZeroDim s) = ZeroBasis
  recomposeEntire ZeroBasis l = (Origin, l)
  decomposeLinMap _ = (ZeroBasis, id)
  recomposeContraLinMap _ _ = LinearMap Origin
  
instance (Num''' s, LinearSpace s) => FiniteDimensional (V0 s) where
  data EntireBasis (V0 s) = V0Basis
  recomposeEntire V0Basis l = (V0, l)
  decomposeLinMap _ = (V0Basis, id)
  recomposeContraLinMap _ _ = LinearMap V0
  
instance FiniteDimensional ℝ where
  data EntireBasis ℝ = RealsBasis
  recomposeEntire RealsBasis [] = (0, [])
  recomposeEntire RealsBasis (μ:cs) = (μ, cs)
  decomposeLinMap (LinearMap v) = (RealsBasis, (v:))
  recomposeContraLinMap fw = LinearMap . fw

#define FreeFiniteDimensional(V, VB, take, give)          \
instance (Num''' s, LSpace s)                              \
            => FiniteDimensional (V s) where {              \
  data EntireBasis (V s) = VB;                               \
  recomposeEntire _ (take:cs) = (give, cs);                   \
  recomposeEntire b cs = recomposeEntire b $ cs ++ [0];        \
  decomposeLinMap (LinearMap m) = (VB, (toList m ++));          \
  recomposeContraLinMap fw mv = LinearMap $ (\v -> fw $ fmap (<.>^v) mv) <$> Mat.identity }
FreeFiniteDimensional(V1, V1Basis, c₀         , V1 c₀         )
FreeFiniteDimensional(V2, V2Basis, c₀:c₁      , V2 c₀ c₁      )
FreeFiniteDimensional(V3, V3Basis, c₀:c₁:c₂   , V3 c₀ c₁ c₂   )
FreeFiniteDimensional(V4, V4Basis, c₀:c₁:c₂:c₃, V4 c₀ c₁ c₂ c₃)
                                  
deriving instance Show (EntireBasis ℝ)
  
instance ( FiniteDimensional u, LinearSpace (DualVector u), DualVector (DualVector u) ~ u
         , FiniteDimensional v, LinearSpace (DualVector v), DualVector (DualVector v) ~ v
         , Scalar u ~ Scalar v, Fractional' (Scalar v) )
            => FiniteDimensional (u,v) where
  data EntireBasis (u,v) = TupleBasis !(EntireBasis u) !(EntireBasis v)
  decomposeLinMap (LinearMap (fu, fv))
       = case (decomposeLinMap (asLinearMap$fu), decomposeLinMap (asLinearMap$fv)) of
         ((bu, du), (bv, dv)) -> (TupleBasis bu bv, du . dv)
  recomposeEntire (TupleBasis bu bv) coefs = case recomposeEntire bu coefs of
                        (u, coefs') -> case recomposeEntire bv coefs' of
                         (v, coefs'') -> ((u,v), coefs'')
  recomposeContraLinMap fw dds
         = recomposeContraLinMap fw (fst<$>dds)
          ⊕ recomposeContraLinMap fw (snd<$>dds)
  
deriving instance (Show (EntireBasis u), Show (EntireBasis v))
                    => Show (EntireBasis (u,v))

infixr 0 \$

-- | Inverse function application, in the sense of providing a
--   /least-squares-error/ solution to a linear equation system.
-- 
--   If you want to solve for multiple RHS vectors, be sure to partially
--   apply this operator to the matrix element.
(\$) :: ( FiniteDimensional u, FiniteDimensional v, SemiInner v
        , Scalar u ~ Scalar v, Fractional' (Scalar v) )
          => (u+>v) -> v -> u
(\$) m = fst . \v -> recomposeEntire mbas [v'<.>^v | v' <- v's]
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m
    

pseudoInverse :: ( FiniteDimensional u, FiniteDimensional v, SemiInner v
                 , Scalar u ~ Scalar v, Fractional' (Scalar v) )
          => (u+>v) -> v+>u
pseudoInverse m = recomposeContraLinMap (fst . recomposeEntire mbas) v's
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m


-- | The <https://en.wikipedia.org/wiki/Riesz_representation_theorem Riesz representation theorem>
--   provides an isomorphism between a Hilbert space and its (continuous) dual space.
riesz :: (FiniteDimensional v, InnerSpace v) => DualVector v -+> v
riesz = LinearFunction $ \dv ->
       let (bas, compos) = decomposeLinMap $ sampleLinearFunction $ applyDualVector $ dv
       in fst . recomposeEntire bas $ compos []

sRiesz :: (FiniteDimensional v, InnerSpace v) => DualSpace v -+> v
sRiesz = LinearFunction $ \dv ->
       let (bas, compos) = decomposeLinMap $ dv
       in fst . recomposeEntire bas $ compos []

coRiesz :: (LSpace v, Num''' (Scalar v), InnerSpace v) => v -+> DualVector v
coRiesz = fromFlatTensor . arr asTensor . sampleLinearFunction . inner

-- | Functions are generally a pain to display, but since linear functionals
--   in a Hilbert space can be represented by /vectors/ in that space,
--   this can be used for implementing a 'Show' instance.
showsPrecAsRiesz :: ( FiniteDimensional v, InnerSpace v, Show v
                    , HasBasis (Scalar v), Basis (Scalar v) ~ () )
                      => Int -> DualSpace v -> ShowS
showsPrecAsRiesz p dv = showParen (p>0) $ ("().<"++)
            . showsPrec 7 (sRiesz$dv)

instance Show (LinearMap ℝ (V0 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V1 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V2 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V3 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V4 ℝ) ℝ) where showsPrec = showsPrecAsRiesz


infixl 7 .<

-- | Outer product of a general @v@-vector and a basis element from @w@.
--   Note that this operation is in general pretty inefficient; it is
--   provided mostly to lay out matrix definitions neatly.
(.<) :: ( FiniteDimensional v, Num''' (Scalar v)
        , InnerSpace v, LSpace w, HasBasis w, Scalar v ~ Scalar w )
           => Basis w -> v -> v+>w
bw .< v = sampleLinearFunction $ LinearFunction $ \v' -> recompose [(bw, v<.>v')]

instance Show (LinearMap s v (V0 s)) where
  show _ = "zeroV"
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V1 ℝ)) where
  showsPrec p m = showParen (p>6) $ ("ex .< "++)
                       . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._x)) $ m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V2 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._x)) $ m)
         . (" ^+^ ey.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._y)) $ m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V3 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._x)) $ m)
         . (" ^+^ ey.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._y)) $ m)
         . (" ^+^ ez.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._z)) $ m)
instance (FiniteDimensional v, InnerSpace v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V4 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._x)) $ m)
         . (" ^+^ ey.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._y)) $ m)
         . (" ^+^ ez.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._z)) $ m)
         . (" ^+^ ew.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._w)) $ m)




-- | A positive definite symmetric bilinear form.
newtype Metric v = Metric { getMetricFn :: v -+> DualVector v }

euclideanMetric :: (LSpace v, InnerSpace v, DualVector v ~ v) => Metric v
euclideanMetric = Metric id

infixl 6 ^%
(^%) :: (LSpace v, Floating (Scalar v)) => v -> Metric v -> v
v ^% Metric m = v ^/ sqrt ((m$v)<.>^v)

metricSq :: LSpace v => Metric v -> v -> Scalar v
metricSq (Metric m) v = (m$v)<.>^v

metric :: (LSpace v, Floating (Scalar v)) => Metric v -> v -> Scalar v
metric m = sqrt . metricSq m


data OrthonormalSystem v = OrthonormalSystem {
      orthonormalityMetric :: Metric v
    , orthonormalVectors :: [v]
    }

orthonormaliseFussily :: (LSpace v, RealFloat (Scalar v))
                           => Metric v -> [v] -> [v]
orthonormaliseFussily me = go []
 where go _ [] = []
       go ws (v₀:vs)
         | mvd > 1/4  = let v = vd^/sqrt mvd
                        in v : go (v:ws) vs
         | otherwise  = go ws vs
        where vd = orthogonalComplementProj me ws $ v₀
              mvd = metricSq me vd

orthogonalComplementProj :: LSpace v => Metric v -> [v] -> (v-+>v)
orthogonalComplementProj (Metric m) ws = LinearFunction $ \v₀
             -> foldl' (\v w -> v ^-^ w^*((m$v)<.>^w)) v₀ ws



data Eigenvector v = Eigenvector {
      ev_Eigenvalue :: Scalar v -- ^ The estimated eigenvalue @λ@.
    , ev_Eigenvector :: v       -- ^ Normalised vector @v@ that gets mapped to a multiple, namely:
    , ev_FunctionApplied :: v   -- ^ @f $ v ≡ λ *^ v @.
    , ev_Deviation :: v         -- ^ Deviation of these two supposedly equivalent expressions.
    , ev_Badness :: Scalar v    -- ^ Norm of the deviation, normalised by the eigenvalue.
    }
deriving instance (Show v, Show (Scalar v)) => Show (Eigenvector v)

constructEigenSystem :: (LSpace v, RealFloat (Scalar v))
      => Metric v           -- ^ The notion of orthonormality.
      -> (v-+>v)            -- ^ Operator to calculate the eigensystem of.
                            --   Must be Hermitian WRT the scalar product
                            --   defined by the given metric.
      -> v                  -- ^ Starting vector for the power method.
      -> [[Eigenvector v]]  -- ^ Infinite sequence of ever more accurate approximations
                            --   to the eigensystem of the operator.
constructEigenSystem me@(Metric m) f = iterate (map asEV
                                           . orthonormaliseFussily (Metric m)
                                           . newSys)
                                         . pure . asEV . (^%me)
 where newSys [] = []
       newSys (Eigenvector λ v fv dv ε : evs)
         | ε>0        = case newSys evs of
                         []     -> [fv^/λ, dv^*(λ/ε)]
                         vn:vns -> fv^/λ : vn : dv^*(abs λ/ε) : vns
         | otherwise  = v : newSys evs
       asEV v = Eigenvector λ v fv dv ε
        where λ = v'<.>^fv
              ε = metric me dv / abs λ
              fv = f $ v
              dv = v^*λ ^-^ fv
              v' = m $ v



roughEigenSystem :: (FiniteDimensional v, RealFloat (Scalar v))
        => Metric v
        -> (v+>v)
        -> [Eigenvector v]
roughEigenSystem me f = go fBas 0 [[]]
 where go [] _ (evs:_) = evs
       go (v:vs) fpε (evs:evss)
         | metric me vPerp > fpε  = case evss of
             []       -> let evss' = constructEigenSystem me (arr f) vPerp
                         in go vs (orthonormalityError me $ ev_Eigenvector<$>head evss')
                                   evss'
             evs':_   -> go (v:vs) (orthonormalityError me $ ev_Eigenvector<$>evs') evss
         | otherwise              = go vs fpε (evs:evss)
        where vPerp = orthogonalComplementProj me (ev_Eigenvector<$>evs) $ v
       fBas = (^%me) <$> snd (decomposeLinMap f) []


orthonormalityError :: LSpace v => Metric v -> [v] -> Scalar v
orthonormalityError me vs = metricSq me $ orthogonalComplementProj me vs $ sumV vs
