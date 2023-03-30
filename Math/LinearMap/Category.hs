-- |
-- Module      : Math.LinearMap.Category
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
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
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE ExplicitNamespaces   #-}

module Math.LinearMap.Category (
            -- * Linear maps
            -- $linmapIntro

            -- ** Function implementation
              LinearFunction (..), type (-+>)(), Bilinear
            , lfun, (-+$>)
            -- ** Tensor implementation
            , LinearMap (..), type (+>)()
            , (⊕), (>+<)
            , adjoint
            -- ** Dual vectors
            -- $dualVectorIntro
            , (<.>^), (-+|>)
            -- * Tensor spaces
            , Tensor (..), type (⊗)(), (⊗)
            -- ** Symmetric
            , SymmetricTensor(..), squareV, squareVs
            , type (⊗〃+>)(), currySymBilin
            -- * Norms
            -- $metricIntro
            , Norm(..), Seminorm
            , spanNorm
            , euclideanNorm
            , (|$|)
            , normSq
            , (<$|)
            , scaleNorm
            , normSpanningSystem
            , normSpanningSystem'
            -- ** Variances
            , Variance, spanVariance, (|&>), varianceSpanningSystem
            , dualNorm, dualNorm', dependence
            -- ** Utility
            , densifyNorm, wellDefinedNorm
            -- * Solving linear equations
            , (\$), pseudoInverse, roughDet
            , linearRegressionW, linearRegression
            , LinearRegressionResult
            , linearFit_χν², linearFit_bestModel, linearFit_modelUncertainty 
            -- * Eigenvalue problems
            , eigen
            , constructEigenSystem
            , roughEigenSystem
            , finishEigenSystem
            , Eigenvector(..)
            -- * The classes of suitable vector spaces
            -- $classesExplanation
            -- ** Deriving from basis
            , module Math.LinearMap.Category.Instances.Deriving
            -- ** The classes
            , module Data.VectorSpace
            , LSpace
            , DimensionAware (..)
            , Dimensional (..)
            , StaticDimensional (..)
            , Dimension
            , TensorSpace (..)
            , LinearSpace (..)
            -- ** Orthonormal systems
            , SemiInner (..), cartesianDualBasisCandidates, embedFreeSubspace
            -- ** Finite baseis
            , FiniteDimensional (..)
            -- * Utility
            -- ** Linear primitives
            , addV, scale, inner, flipBilin, bilinearFunction
            -- ** Tensors with basis decomposition
            , (.⊗)
            -- ** Hilbert space operations
            , (·), DualSpace, riesz, coRiesz, showsPrecAsRiesz, (.<)
            -- ** Standard decompositions
            , TensorDecomposable(..), RieszDecomposable(..)
            , tensorDecomposeShowsPrec, rieszDecomposeShowsPrec
            -- ** Constraint synonyms
            , HilbertSpace, SimpleSpace, RealSpace
            , Num'(..)
            , Fractional'
            , RealFrac', RealFloat', LinearShowable
            -- ** Coercions
            , VSCCoercion(..)
            -- ** Double-dual, scalar-scalar etc. identity
            , ClosedScalarWitness(..), TrivialTensorWitness(..)
            , ScalarSpaceWitness(..), DualSpaceWitness(..), LinearManifoldWitness(..)
            , DualFinitenessWitness(..)
            -- ** Misc
            , relaxNorm, transformNorm, transformVariance
            , findNormalLength, normalLength
            , summandSpaceNorms, sumSubspaceNorms
            , sharedNormSpanningSystem, sharedSeminormSpanningSystem
            , sharedSeminormSpanningSystem'
            , convexPolytopeHull
            , symmetricPolytopeOuterVertices
            ) where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Category.Instances.Deriving
import Math.LinearMap.Asserted
import Math.VectorSpace.DimensionAware
import Math.VectorSpace.Docile
import Math.LinearMap.Category.TensorQuot

import Data.Tree (Tree(..), Forest)
import Data.List (sortBy, foldl')
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Ord (comparing)
import Data.List (maximumBy)
import Data.Maybe (catMaybes)
import Data.Foldable (toList)
import Data.Semigroup

import Data.VectorSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained

import Linear ( V0(V0), V1(V1), V2(V2), V3(V3), V4(V4)
              , _x, _y, _z, _w )
import Data.VectorSpace.Free
import Math.VectorSpace.ZeroDimensional
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import Control.Lens ((^.))

import qualified Data.Vector.Unboxed as UArr

import Numeric.IEEE

import qualified GHC.Exts as GHC
import qualified Data.Type.Coercion as GHC

-- $linmapIntro
-- This library deals with linear functions, i.e. functions @f :: v -> w@
-- that fulfill
-- 
-- @
-- f $ μ 'Data.VectorSpace.^*' u 'Data.AdditiveGroup.^+^' v ≡ μ ^* f u ^+^ f v    ∀ u,v :: v;  μ :: 'Scalar' v
-- @
-- 
-- Such functions form a cartesian monoidal category (in maths called 
-- <https://en.wikipedia.org/wiki/Category_of_modules#Example:_the_category_of_vector_spaces VectK>).
-- This is implemented by 'Control.Arrow.Constrained.PreArrow', which is the
-- preferred interface for dealing with these mappings. The basic
-- “matrix operations” are then:
-- 
-- * Identity matrix: 'Control.Category.Constrained.id'
-- * Matrix addition: 'Data.AdditiveGroup.^+^' (linear maps form an ordinary vector space)
-- * Matrix-matrix multiplication: 'Control.Category.Constrained.<<<'
--     (or '>>>' or 'Control.Category.Constrained..')
-- * Matrix-vector multiplication: 'Control.Arrow.Constrained.$'
-- * Vertical matrix concatenation: 'Control.Arrow.Constrained.&&&'
-- * Horizontal matrix concatenation: '⊕' (aka '>+<')
-- 
-- But linear mappings need not necessarily be implemented as matrices:


-- $dualVectorIntro
-- A @'DualVector' v@ is a linear functional or
-- <https://en.wikipedia.org/wiki/Linear_form linear form> on the vector space @v@,
-- i.e. it is a linear function from the vector space into its scalar field.
-- However, these functions form themselves a vector space, known as the dual space.
-- In particular, the dual space of any 'InnerSpace' is isomorphic to the
-- space itself.
-- 
-- (More precisely: the continuous dual space of a
-- <https://en.wikipedia.org/wiki/Hilbert_space Hilbert space> is isomorphic to
-- that Hilbert space itself; see the 'riesz' isomorphism.)
-- 
-- As a matter of fact, in many applications, no distinction is made between a
-- space and its dual. Indeed, we have for the basic 'LinearSpace' instances
-- @'DualVector' v ~ v@, and '<.>^' is simply defined as a scalar product.
-- In this case, a general 'LinearMap' is just a tensor product / matrix.
-- 
-- However, scalar products are often not as natural as they are made to look:
-- 
-- * A scalar product is only preserved under orthogonal transformations.
--   It is not preserved under scalings, and certainly not under general linear
--   transformations. This is very important in applications such as relativity
--   theory (here, people talk about /covariant/ vs /contravariant/ tensors),
--   but also relevant for more mundane
--   <http://hackage.haskell.org/package/manifolds manifolds> like /sphere surfaces/:
--   on such a surface, the natural symmetry transformations do generally
--   not preserve a scalar product you might define.
-- 
-- * There may be more than one meaningful scalar product. For instance,
--   the <https://en.wikipedia.org/wiki/Sobolev_space Sobolev space> of weakly
--   differentiable functions also permits the
--   <https://en.wikipedia.org/wiki/Square-integrable_function 𝐿²> scalar product
--   – each has different and useful properties.
-- 
-- Neither of this is a problem if we keep the dual space a separate type.
-- Effectively, this enables the type system to prevent you from writing code that
-- does not behave natural (i.e. that depends on a concrete choice of basis / scalar
-- product).
-- 
-- For cases when you do have some given notion of orientation/scale in a vector space
-- and need it for an algorithm, you can always provide a 'Norm', which is essentially
-- a reified scalar product.
-- 
-- Note that @DualVector (DualVector v) ~ v@ in any 'LSpace': the /double-dual/
-- space is /naturally/ isomorphic to the original space, by way of
-- 
-- @
-- v '<.>^' dv  ≡  dv '<.>^' v
-- @



-- | A linear map that simply projects from a dual vector in @u@ to a vector in @v@.
-- 
-- @
-- (du '-+|>' v) u  ≡  v '^*' (du '<.>^' u)
-- @
infixr 7 -+|>
(-+|>) :: ( EnhancedCat f (LinearFunction s)
          , LSpace u, LSpace v, Scalar u ~ s, Scalar v ~ s
          , Object f u, Object f v )
             => DualVector u -> v -> f u v
du-+|>v = arr . LinearFunction $ (v^*) . (du<.>^)




-- $metricIntro
-- A norm is a way to quantify the magnitude/length of different vectors,
-- even if they point in different directions.
-- 
-- In an 'InnerSpace', a norm is always given by the scalar product,
-- but there are spaces without a canonical scalar product (or situations
-- in which this scalar product does not give the metric you want). Hence,
-- we let the functions like 'constructEigenSystem', which depend on a norm
-- for orthonormalisation, accept a 'Norm' as an extra argument instead of
-- requiring 'InnerSpace'.

-- | A seminorm defined by
-- 
-- @
-- ‖v‖ = √(∑ᵢ ⟨dᵢ|v⟩²)
-- @
-- 
-- for some dual vectors @dᵢ@. If given a complete basis of the dual space,
-- this generates a proper 'Norm'.
-- 
-- If the @dᵢ@ are a complete orthonormal system, you get the 'euclideanNorm'
-- (in an inefficient form).
spanNorm :: ∀ v . LSpace v => [DualVector v] -> Seminorm v
spanNorm = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness
        -> \dvs -> Norm . LinearFunction $ \v -> sumV [dv ^* (dv<.>^v) | dv <- dvs]

spanVariance :: ∀ v . LSpace v => [v] -> Variance v
spanVariance = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> spanNorm

-- | Modify a norm in such a way that the given vectors lie within its unit ball.
--   (Not /optimally/ – the unit ball may be bigger than necessary.)
relaxNorm :: ∀ v . SimpleSpace v => Norm v -> [v] -> Norm v
relaxNorm = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness
        -> \me vs -> let vs' = normSpanningSystem' me
                     in dualNorm . spanVariance $ vs' ++ vs

-- | Scale the result of a norm with the absolute of the given number.
-- 
-- @
-- scaleNorm μ n |$| v = abs μ * (n|$|v)
-- @
-- 
-- Equivalently, this scales the norm's unit ball by the reciprocal of that factor.
scaleNorm :: ∀ v . LSpace v => Scalar v -> Norm v -> Norm v
scaleNorm = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness -> \μ (Norm n) -> Norm $ μ^2 *^ n

-- | A positive (semi)definite symmetric bilinear form. This gives rise
--   to a <https://en.wikipedia.org/wiki/Norm_(mathematics) norm> thus:
-- 
--   @
--   'Norm' n '|$|' v = √(n v '<.>^' v)
--   @
--   
--   Strictly speaking, this type is neither strong enough nor general enough to
--   deserve the name 'Norm': it includes proper 'Seminorm's (i.e. @m|$|v ≡ 0@ does
--   not guarantee @v == zeroV@), but not actual norms such as the ℓ₁-norm on ℝⁿ
--   (Taxcab norm) or the supremum norm.
--   However, 𝐿₂-like norms are the only ones that can really be formulated without
--   any basis reference; and guaranteeing positive definiteness through the type
--   system is scarcely practical.
newtype Norm v = Norm {
    applyNorm :: v -+> DualVector v
  }

-- | A “norm” that may explicitly be degenerate, with @m|$|v ⩵ 0@ for some @v ≠ zeroV@.
type Seminorm v = Norm v

-- | @(m<>n|$|v)^2 ⩵ (m|$|v)^2 + (n|$|v)^2@
instance ∀ v . LSpace v => Semigroup (Norm v) where
  Norm m <> Norm n = case dualSpaceWitness @v of
    DualSpaceWitness -> Norm $ m^+^n
-- | @mempty|$|v ≡ 0@
instance ∀ v . LSpace v => Monoid (Seminorm v) where
  mempty = case dualSpaceWitness @v of
    DualSpaceWitness -> Norm zeroV
  mappend = (<>)

-- | A multidimensional variance of points @v@ with some distribution can be
--   considered a norm on the dual space, quantifying for a dual vector @dv@ the
--   expectation value of @(dv<.>^v)^2@.
type Variance v = Norm (DualVector v)

-- | The canonical standard norm (2-norm) on inner-product / Hilbert spaces.
euclideanNorm :: HilbertSpace v => Norm v
euclideanNorm = Norm id

-- | The norm induced from the (arbitrary) choice of basis in a finite space.
--   Only use this in contexts where you merely need /some/ norm, but don't
--   care if it might be biased in some unnatural way.
adhocNorm :: FiniteDimensional v => Norm v
adhocNorm = Norm uncanonicallyToDual

-- | A proper norm induces a norm on the dual space – the “reciprocal norm”.
--   (The orthonormal systems of the norm and its dual are mutually conjugate.)
--   The dual norm of a seminorm is undefined.
dualNorm :: SimpleSpace v => Norm v -> Variance v
dualNorm = spanVariance . normSpanningSystem'

-- | 'dualNorm' in the opposite direction. This is actually self-inverse;
--    with 'dualSpaceWitness' you can replace each with the other direction.
dualNorm' :: ∀ v . SimpleSpace v => Variance v -> Norm v
dualNorm' = case dualSpaceWitness :: DualSpaceWitness v of
     DualSpaceWitness -> spanNorm . normSpanningSystem'

transformNorm :: ∀ v w . (LSpace v, LSpace w, Scalar v~Scalar w)
                             => (v+>w) -> Norm w -> Norm v
transformNorm = case ( dualSpaceWitness :: DualSpaceWitness v
                     , dualSpaceWitness :: DualSpaceWitness w ) of
    (DualSpaceWitness, DualSpaceWitness)
            -> \f (Norm m) -> Norm . arr $ (adjoint $ f) . (fmap m $ f)

transformVariance :: ∀ v w . (LSpace v, LSpace w, Scalar v~Scalar w)
                        => (v+>w) -> Variance v -> Variance w
transformVariance = case ( dualSpaceWitness :: DualSpaceWitness v
                     , dualSpaceWitness :: DualSpaceWitness w ) of
    (DualSpaceWitness, DualSpaceWitness)
            -> \f (Norm m) -> Norm . arr $ f . (fmap m $ adjoint $ f)

infixl 6 ^%
(^%) :: (LSpace v, Floating (Scalar v)) => v -> Norm v -> v
v ^% Norm m = v ^/ sqrt ((m-+$>v)<.>^v)

-- | The unique positive number whose norm is 1 (if the norm is not constant zero).
findNormalLength :: ∀ s . RealFrac' s => Norm s -> Maybe s
findNormalLength (Norm m) = case ( closedScalarWitness :: ClosedScalarWitness s
                                 , m-+$>1 ) of
   (ClosedScalarWitness, o) | o > 0      -> Just . sqrt $ recip o
                            | otherwise  -> Nothing

-- | Unsafe version of 'findNormalLength', only works reliable if the norm
--   is actually positive definite.
normalLength :: ∀ s . RealFrac' s => Norm s -> s
normalLength (Norm m) = case ( closedScalarWitness :: ClosedScalarWitness s
                             , m-+$>1 ) of
   (ClosedScalarWitness, o) | o >= 0     -> sqrt $ recip o
                            | o < 0      -> error "Norm fails to be positive semidefinite."
                            | otherwise  -> error "Norm yields NaN."

infixr 0 <$|, |$|
-- | “Partially apply” a norm, yielding a dual vector
--   (i.e. a linear form that accepts the second argument of the scalar product).
-- 
-- @
-- ('euclideanNorm' '<$|' v) '<.>^' w  ≡  v '<.>' w
-- @
-- 
--   See also '|&>'.
(<$|) :: LSpace v => Norm v -> v -> DualVector v
Norm m <$| v = m-+$>v

-- | The squared norm. More efficient than '|$|' because that needs to take
--   the square root.
normSq :: LSpace v => Seminorm v -> v -> Scalar v
normSq (Norm m) v = (m-+$>v)<.>^v

-- | Use a 'Norm' to measure the length / norm of a vector.
-- 
-- @
-- 'euclideanNorm' |$| v  ≡  √(v '<.>' v)
-- @
(|$|) :: (LSpace v, Floating (Scalar v)) => Seminorm v -> v -> Scalar v
(|$|) m = sqrt . normSq m

infixl 1 |&>
-- | Flipped, “ket” version of '<$|'.
-- 
-- @
-- v '<.>^' (w |&> 'euclideanNorm')  ≡  v '<.>' w
-- @
(|&>) :: ∀ v . LSpace v => DualVector v -> Variance v -> v
dv |&> Norm m = case dualSpaceWitness @v of
   DualSpaceWitness -> m-+$>dv


-- | 'spanNorm' / 'spanVariance' are inefficient if the number of vectors
--   is similar to the dimension of the space, or even larger than it.
--   Use this function to optimise the underlying operator to a dense
--   matrix representation.
densifyNorm :: ∀ v . LSpace v => Norm v -> Norm v
densifyNorm = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness
        -> \(Norm m) -> Norm . arr $ sampleLinearFunction $ m

-- | Like 'densifyNorm', but also perform a “sanity check” to eliminate NaN etc. problems.
wellDefinedNorm :: ∀ v . LinearSpace v => Norm v -> Maybe (Norm v)
wellDefinedNorm = case dualSpaceWitness :: DualSpaceWitness v of
    DualSpaceWitness
        -> \(Norm m) -> Norm <$> wellDefinedVector m

data OrthonormalSystem v = OrthonormalSystem {
      orthonormalityNorm :: Norm v
    , orthonormalVectors :: [v]
    }

orthonormaliseFussily :: ∀ v . (LSpace v, RealFloat (Scalar v))
                           => Scalar v -> Norm v -> [v] -> [v]
orthonormaliseFussily = onf dualSpaceWitness
 where onf :: DualSpaceWitness v -> Scalar v -> Norm v -> [v] -> [v]
       onf DualSpaceWitness fuss me = go []
        where go _ [] = []
              go ws (v₀:vs)
                | mvd > fuss  = let μ = 1/sqrt mvd
                                    v = vd^*μ
                                in v : go ((v,dvd^*μ):ws) vs
                | otherwise   = go ws vs
               where vd = orthogonalComplementProj' ws $ v₀
                     dvd = applyNorm me $ vd
                     mvd = dvd<.>^vd

orthogonalComplementProj' :: LSpace v => [(v, DualVector v)] -> (v-+>v)
orthogonalComplementProj' ws = LinearFunction $ \v₀
             -> foldl' (\v (w,dw) -> v ^-^ w^*(dw<.>^v)) v₀ ws

orthogonalComplementProj :: LSpace v => Norm v -> [v] -> (v-+>v)
orthogonalComplementProj (Norm m)
      = orthogonalComplementProj' . map (id &&& (m-+$>))


-- | A space in which you can use '·' both for scaling with a real number,
--   and as dot-product for obtaining such a number.
type RealSpace v = ( LinearSpace v, Scalar v ~ ℝ
                   , TensorQuot v ℝ, (v⨸ℝ) ~ DualVector v
                   , TensorQuot v v, (v⨸v) ~ ℝ )


data Eigenvector v = Eigenvector {
      ev_Eigenvalue :: Scalar v -- ^ The estimated eigenvalue @λ@.
    , ev_Eigenvector :: v       -- ^ Normalised vector @v@ that gets mapped to a multiple, namely:
    , ev_FunctionApplied :: v   -- ^ @f $ v ≡ λ *^ v @.
    , ev_Deviation :: v         -- ^ Deviation of @v@ to @(f$v)^/λ@. Ideally, this would of course be equal.
    , ev_Badness :: Scalar v    -- ^ Squared norm of the deviation.
    }
deriving instance (Show v, Show (Scalar v)) => Show (Eigenvector v)

-- | Lazily compute the eigenbasis of a linear map. The algorithm is essentially
--   a hybrid of Lanczos/Arnoldi style Krylov-spanning and QR-diagonalisation,
--   which we don't do separately but /interleave/ at each step.
-- 
--   The size of the eigen-subbasis increases with each step until the space's
--   dimension is reached. (But the algorithm can also be used for
--   infinite-dimensional spaces.)
constructEigenSystem :: (LSpace v, RealFloat (Scalar v))
      => Norm v           -- ^ The notion of orthonormality.
      -> Scalar v           -- ^ Error bound for deviations from eigen-ness.
      -> (v-+>v)            -- ^ Operator to calculate the eigensystem of.
                            --   Must be Hermitian WRT the scalar product
                            --   defined by the given metric.
      -> [v]                -- ^ Starting vector(s) for the power method.
      -> [[Eigenvector v]]  -- ^ Infinite sequence of ever more accurate approximations
                            --   to the eigensystem of the operator.
constructEigenSystem me ε₀ f = iterate (
                                             sortBy (comparing $
                                               negate . abs . ev_Eigenvalue)
                                           . map asEV
                                           . orthonormaliseFussily (1/4) me
                                           . newSys)
                                         . map (asEV . (^%me))
 where newSys [] = []
       newSys (Eigenvector λ v fv dv ε : evs)
         | ε>ε₀       = case newSys evs of
                         []     -> [fv^/λ, dv^/sqrt(ε+ε₀)]
                         vn:vns -> fv^/λ : vn : dv^/sqrt(ε+ε₀) : vns
         | ε>=0       = v : newSys evs
         | otherwise  = newSys evs
       asEV v = Eigenvector λ v fv dv ε
        where λ² = fv'<.>^fv
              λ = fv'<.>^v
              ε = normSq me dv
              fv = f $ v
              fv' = me<$|fv
              dv | λ²>0       = v ^-^ fv^*(λ/λ²) -- for stability reasons
                 | otherwise  = zeroV


finishEigenSystem :: ∀ v . (LSpace v, RealFloat (Scalar v))
                      => Norm v -> [Eigenvector v] -> [Eigenvector v]
finishEigenSystem me = go . sortBy (comparing $ negate . ev_Eigenvalue)
 where go [] = []
       go [v] = [v]
       go vs@[Eigenvector λ₀ v₀ fv₀ _dv₀ _ε₀, Eigenvector λ₁ v₁ fv₁ _dv₁ _ε₁]
          | λ₀>λ₁      = [ asEV v₀' fv₀', asEV v₁' fv₁' ]
          | otherwise  = vs
        where
              v₀' = v₀^*μ₀₀ ^+^ v₁^*μ₀₁
              fv₀' = fv₀^*μ₀₀ ^+^ fv₁^*μ₀₁
              
              v₁' = v₀^*μ₁₀ ^+^ v₁^*μ₁₁
              fv₁' = fv₀^*μ₁₀ ^+^ fv₁^*μ₁₁
              
              fShift₁v₀ = fv₀ ^-^ λ₁*^v₀
              
              (μ₀₀,μ₀₁) = normalised ( λ₀ - λ₁
                                     , (me <$| fShift₁v₀)<.>^v₁ )
              (μ₁₀,μ₁₁) = (-μ₀₁, μ₀₀)
        
       go evs = lo'' ++ upper'
        where l = length evs
              lChunk = l`quot`3
              (loEvs, (midEvs, hiEvs)) = second (splitAt $ l - 2*lChunk)
                                                    $ splitAt lChunk evs
              (lo',hi') = splitAt lChunk . go $ loEvs++hiEvs
              (lo'',mid') = splitAt lChunk . go $ lo'++midEvs
              upper'  = go $ mid'++hi'
       
       asEV v fv = Eigenvector λ v fv dv ε
        where λ = (me<$|v)<.>^fv
              dv = v^*λ ^-^ fv
              ε = normSq me dv / λ^2
       
       normalised (x,y) = (x/r, y/r)
        where r = sqrt $ x^2 + y^2

-- | Find a system of vectors that approximate the eigensytem, in the sense that:
--   each true eigenvalue is represented by an approximate one, and that is closer
--   to the true value than all the other approximate EVs.
-- 
--   This function does not make any guarantees as to how well a single eigenvalue
--   is approximated, though.
roughEigenSystem :: (FiniteDimensional v, IEEE (Scalar v))
        => Norm v
        -> (v+>v)
        -> [Eigenvector v]
roughEigenSystem me f = go fBas 0 [[]]
 where go [] _ (_:evs:_) = evs
       go [] _ (evs:_) = evs
       go (v:vs) oldDim (evs:evss)
         | normSq me vPerp > fpε  = case evss of
             evs':_ | length evs' > oldDim
               -> go (v:vs) (length evs) evss
             _ -> let evss' = tail . constructEigenSystem me fpε (arr f)
                                $ map ev_Eigenvector (head $ evss++[evs]) ++ [vPerp]
                  in go vs (length evs) evss'
         | otherwise              = go vs oldDim (evs:evss)
        where vPerp = orthogonalComplementProj me (ev_Eigenvector<$>evs) $ v
       fBas = (^%me) <$> snd (decomposeLinMap id) []
       fpε = epsilon * 8

-- | Simple automatic finding of the eigenvalues and -vectors
--   of a Hermitian operator, in reasonable approximation.
-- 
--   This works by spanning a QR-stabilised Krylov basis with 'constructEigenSystem'
--   until it is complete ('roughEigenSystem'), and then properly decoupling the
--   system with 'finishEigenSystem' (based on two iterations of shifted Givens rotations).
--   
--   This function is a tradeoff in performance vs. accuracy. Use 'constructEigenSystem'
--   and 'finishEigenSystem' directly for more quickly computing a (perhaps incomplete)
--   approximation, or for more precise results.
eigen :: (FiniteDimensional v, HilbertSpace v, IEEE (Scalar v))
               => (v+>v) -> [(Scalar v, v)]
eigen f = map (ev_Eigenvalue &&& ev_Eigenvector)
   $ iterate (finishEigenSystem euclideanNorm) (roughEigenSystem euclideanNorm f) !! 2


-- | Approximation of the determinant.
roughDet :: (FiniteDimensional v, IEEE (Scalar v)) => (v+>v) -> Scalar v
roughDet = roughEigenSystem adhocNorm >>> map ev_Eigenvalue >>> product


orthonormalityError :: LSpace v => Norm v -> [v] -> Scalar v
orthonormalityError me vs = normSq me $ orthogonalComplementProj me vs $ sumV vs


normSpanningSystem :: SimpleSpace v
               => Seminorm v -> [DualVector v]
normSpanningSystem = map snd . normSpanningSystems

normSpanningSystems :: SimpleSpace v
               => Seminorm v -> [(v, DualVector v)]
normSpanningSystems me@(Norm m)
     = catMaybes . map (\(v,d)->(v,)<$>d) . orthonormaliseDuals 0
         . map (id&&&(m-+$>)) $ normSpanningSystem' me

normSpanningSystem' :: (FiniteDimensional v, IEEE (Scalar v))
               => Seminorm v -> [v]
normSpanningSystem' me = orthonormaliseFussily 0 me $ enumerateSubBasis entireBasis

-- | Inverse of 'spanVariance'. Equivalent to 'normSpanningSystem' on the dual space.
varianceSpanningSystem :: ∀ v . SimpleSpace v => Variance v -> [v]
varianceSpanningSystem = case dualSpaceWitness :: DualSpaceWitness v of
                           DualSpaceWitness -> normSpanningSystem

-- | For any two norms, one can find a system of co-vectors that, with suitable
--   coefficients, spans /either/ of them: if @shSys = sharedNormSpanningSystem n₀ n₁@,
--   then
-- 
-- @
-- n₀ = 'spanNorm' $ fst<$>shSys
-- @
-- 
-- and
-- 
-- @
-- n₁ = 'spanNorm' [dv^*η | (dv,η)<-shSys]
-- @
-- 
-- A rather crude approximation ('roughEigenSystem') is used in this function, so do
-- not expect the above equations to hold with great accuracy.
sharedNormSpanningSystem :: SimpleSpace v
               => Norm v -> Seminorm v -> [(DualVector v, Scalar v)]
sharedNormSpanningSystem nn@(Norm n) nm
      = first (n-+$>) <$> sharedNormSpanningSystem' 0 (nn, dualNorm nn) nm

sharedNormSpanningSystem' :: ∀ v . SimpleSpace v
               => Int -> (Norm v, Variance v) -> Seminorm v -> [(v, Scalar v)]
sharedNormSpanningSystem' = snss dualSpaceWitness
 where snss :: DualSpaceWitness v -> Int -> (Norm v, Variance v)
                     -> Seminorm v -> [(v, Scalar v)]
       snss DualSpaceWitness nRefine (nn@(Norm n), Norm n') (Norm m)
           = sep =<< iterate (finishEigenSystem nn)
                        (roughEigenSystem nn $ arr n' . arr m) !! nRefine
       sep (Eigenvector λ v λv _ _)
         | λ>=0       = [(v, sqrt λ)]
         | otherwise  = []

-- | Like 'sharedNormSpanningSystem n₀ n₁', but allows /either/ of the norms
--   to be singular.
-- 
-- @
-- n₀ = 'spanNorm' [dv | (dv, Just _)<-shSys]
-- @
-- 
-- and
-- 
-- @
-- n₁ = 'spanNorm' $ [dv^*η | (dv, Just η)<-shSys]
--                 ++ [ dv | (dv, Nothing)<-shSys]
-- @
-- 
-- You may also interpret a @Nothing@ here as an “infinite eigenvalue”, i.e.
-- it is so small as an spanning vector of @n₀@ that you would need to scale it
-- by ∞ to use it for spanning @n₁@.
sharedSeminormSpanningSystem :: ∀ v . SimpleSpace v
               => Seminorm v -> Seminorm v -> [(DualVector v, Maybe (Scalar v))]
sharedSeminormSpanningSystem nn nm
         = finalise dualSpaceWitness
               <$> sharedNormSpanningSystem' 1 (combined, dualNorm combined) nn
 where combined = densifyNorm $ nn<>nm
       finalise :: DualSpaceWitness v -> (v, Scalar v) -> (DualVector v, Maybe (Scalar v))
       finalise DualSpaceWitness (v, μn)
           | μn^2 > epsilon  = (v'^*μn, Just $ sqrt (max 0 $ 1 - μn^2)/μn)
           | otherwise       = (v', Nothing)
        where v' = combined<$|v

-- | A system of vectors which are orthogonal with respect to both of the given
--   seminorms. (In general they are not /orthonormal/ to either of them.)
sharedSeminormSpanningSystem' :: ∀ v .  SimpleSpace v
               => Seminorm v -> Seminorm v -> [v]
sharedSeminormSpanningSystem' nn nm
         = fst <$> sharedNormSpanningSystem' 1 (combined, dualNorm combined) nn
 where combined = densifyNorm $ nn<>nm


-- | Interpret a variance as a covariance between two subspaces, and
--   normalise it by the variance on @u@. The result is effectively
--   the linear regression coefficient of a simple regression of the vectors
--   spanning the variance.
dependence :: ∀ u v . (SimpleSpace u, SimpleSpace v, Scalar u~Scalar v)
                => Variance (u,v) -> (u+>v)
dependence = case ( dualSpaceWitness :: DualSpaceWitness u
                  , dualSpaceWitness :: DualSpaceWitness v ) of
  (DualSpaceWitness,DualSpaceWitness)
        -> \(Norm m) -> fmap ( snd . m . (id&&&zeroV) )
              $ pseudoInverse (arr $ fst . m . (id&&&zeroV))


summandSpaceNorms :: ∀ u v . (SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v)
                       => Norm (u,v) -> (Norm u, Norm v)
summandSpaceNorms = case ( dualSpaceWitness :: DualSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness v ) of
  (DualSpaceWitness,DualSpaceWitness)
        -> \nuv -> let spanSys = normSpanningSystem nuv
                   in ( densifyNorm $ spanNorm (fst<$>spanSys)
                      , densifyNorm $ spanNorm (snd<$>spanSys) )

sumSubspaceNorms :: ∀ u v . (LSpace u, LSpace v, Scalar u~Scalar v)
                         => Norm u -> Norm v -> Norm (u,v)
sumSubspaceNorms = case ( dualSpaceWitness :: DualSpaceWitness u
                         , dualSpaceWitness :: DualSpaceWitness v ) of
  (DualSpaceWitness,DualSpaceWitness)
        -> \(Norm nu) (Norm nv) -> Norm $ nu *** nv





instance (SimpleSpace v, Show (DualVector v)) => Show (Norm v) where
  showsPrec p n = showParen (p>9) $ ("spanNorm "++) . shows (normSpanningSystem n)

type LinearShowable v = (Show v, RieszDecomposable v)



convexPolytopeHull :: ∀ v . SimpleSpace v => [v] -> [DualVector v]
convexPolytopeHull vs = case dualSpaceWitness :: DualSpaceWitness v of
         DualSpaceWitness
             -> [dv^/η | (dv,η) <- candidates, all ((<=η) . (dv<.>^)) vs]
 where vrv = spanVariance vs
       nmv = dualNorm' vrv
       candidates :: [(DualVector v, Scalar v)]
       candidates = [ (dv, dv<.>^v) | v <- vs
                                   , let dv = nmv<$|v ]

symmetricPolytopeOuterVertices :: ∀ v . SimpleSpace v => [DualVector v] -> [v]
symmetricPolytopeOuterVertices dvs
         = [ seekExtreme zeroV group | group <- candidates ]
 where nmv :: Norm v
       nmv = spanNorm dvs
       vrv = dualNorm nmv
       withSomeVect :: [(DualVector v, v)]
       withSomeVect = [ (dv, v) | dv <- dvs
                                , let v = dv|&>vrv ]
       (candidates, _) = multiSplit d (2*d) . concat . deinterlacions $ withSomeVect
       d = subbasisDimension (entireBasis :: SubBasis v)
       seekExtreme p₀ [] = p₀
       seekExtreme p₀ ((dv, v) : cs)
           = seekExtreme (p₀^+^vn) [(dw, w ^-^ v^*((dv<.>^w) / lv)) | (dw, w) <- cs]
        where vn = v ^* ((1 - dv<.>^p₀) / lv)
              lv = dv<.>^v

deinterlacions :: SimpleSpace a => [(DualVector a, a)] -> [[(DualVector a, a)]]
deinterlacions l = l : deinterlacions (e ++ map negateV o)
 where (e,o) = deinterlace l
       deinterlace (a:b:xs) = (a:)***(b:) $ deinterlace xs
       deinterlace xs = ([],xs)
       
-- | Simple wrapper of 'linearRegression'.
linearRegressionW :: ∀ s x m y
    . ( LinearSpace x, SimpleSpace y, SimpleSpace m
      , Scalar x ~ s, Scalar y ~ s, Scalar m ~ s, RealFrac' s )
         => Norm y -> (x -> (m +> y)) -> [(x,y)] -> m
linearRegressionW σy modelMap = linearFit_bestModel
                                   . linearRegression modelMap . map (second (,σy))

data LinearRegressionResult x y m = LinearRegressionResult {
          linearFit_χν² :: Scalar m 
           -- ^ How well the data uncertainties match the deviations from the model's
           --   synthetic data.
           -- @
           -- χν² = 1/ν · ∑ δy² / σy²
           -- @
           --   Where @ν@ is the number of degrees of freedom (data values minus model
           --   parameters), @δy = m x - yd@ is the deviation from given data to
           --   the data the model would predict (for each sample point), and @σy@ is
           --   the a-priori measurement uncertainty of the data points. 
           -- 
           --   Values @χν²>1@ indicate that the data could not be described satisfyingly;
           --   @χν²≪1@ suggests overfitting or that the data uncertainties have
           --   been postulated too high.
           -- 
           -- <http://adsabs.harvard.edu/abs/1997ieas.book.....T>
           -- 
           --   If the model is exactly determined or even underdetermined (i.e. @ν≤0@)
           --   then @χν²@ is undefined.
        , linearFit_bestModel :: m
           -- ^ The model that best corresponds to the data, in a least-squares
           --   sense WRT the supplied norm on the data points. In other words,
           --   this is the model that minimises @∑ δy² / σy²@.
        , linearFit_modelUncertainty :: Norm m
        }

linearRegressionWVar :: ∀ s x m y
    . ( LinearSpace x, FiniteDimensional y, SimpleSpace m
      , Scalar x ~ s, Scalar y ~ s, Scalar m ~ s, RealFrac' s )
         => (x -> (m +> y)) -> [(x, (y, Norm y))] -> (m, [DualVector m])
linearRegressionWVar = case True of False -> undefined

linearRegression :: ∀ s x m y
    . ( LinearSpace x, SimpleSpace y, SimpleSpace m
      , Scalar x ~ s, Scalar y ~ s, Scalar m ~ s, RealFrac' s )
         => (x -> (m +> y)) -> [(x, (y, Norm y))] -> LinearRegressionResult x y m
linearRegression = lrw (dualSpaceWitness, dualSpaceWitness)
 where lrw :: (DualSpaceWitness y, DualSpaceWitness m)
                -> (x -> (m +> y)) -> [(x, (y, Norm y))] -> LinearRegressionResult x y m
       lrw (DualSpaceWitness, DualSpaceWitness) modelMap dataxy
         = LinearRegressionResult (χ²/fromIntegral ν) leastSquareSol σm
        where leastSquareSol = (lfun $ forward' . zipWith ((<$|) . snd . snd) dataxy
                                          . forward)
                                 \$ forward' [σy<$|y | (_,(y,σy)) <- dataxy]
              χ² = sum [normSq σy δy | (x, (yd, σy)) <- dataxy
                                     , let δy = yd ^-^ (modelMap x $ leastSquareSol) ]
              ν = length dataxy * subbasisDimension (entireBasis :: SubBasis y)
                  - subbasisDimension (entireBasis :: SubBasis m)
              forward :: m -> [y]
              forward m = [modelMap x $ m | (x,_)<-dataxy]
              forward' :: [DualVector y] -> DualVector m
              forward' = sumV . zipWith (($) . snd) modelGens
              modelGens :: [(m +> y, DualVector y +> DualVector m)]
              modelGens = ((id&&&arr adjoint) . modelMap . fst)<$>dataxy
              σm :: Norm m
              σm = mconcat [ Norm . arr $ m . (fmap ny $ m')
                           | ((_,(_,Norm ny)), (m',m)) <- zip dataxy modelGens ]
                  
-- $classesExplanation
-- To facilitate this library's abstract, base-less approach, the
-- spaces/types need to be instances of multiple typeclasses which
-- are rather tedious to write instances for. Due to the use of type
-- families, GHC's various deriving mechanisms cannot help much with this
-- either.
--
-- In the common case that your spaces /do/ have a canonical basis, the
-- instances can be generated automatically with one of the Template Haskell
-- macros 'makeLinearSpaceFromBasis' or 'makeFiniteDimensionalFromBasis'.
