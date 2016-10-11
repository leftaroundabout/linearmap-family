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
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE ExplicitNamespaces   #-}

module Math.LinearMap.Category (
            -- * Linear maps
            -- $linmapIntro

            -- ** Function implementation
              LinearFunction (..), type (-+>)(), Bilinear
            -- ** Tensor implementation
            , LinearMap (..), type (+>)()
            , (⊕), (>+<)
            , adjoint
            -- ** Dual vectors
            -- $dualVectorIntro
            , (<.>^)
            -- * Tensor spaces
            , Tensor (..), type (⊗)(), (⊗)
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
            , Variance, spanVariance, dualNorm
            , dependence
            -- ** Utility
            , densifyNorm
            -- * Solving linear equations
            , (\$), pseudoInverse, roughDet
            -- * Eigenvalue problems
            , eigen
            , constructEigenSystem
            , roughEigenSystem
            , finishEigenSystem
            , Eigenvector(..)
            -- * The classes of suitable vector spaces
            , LSpace
            , TensorSpace (..)
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
            -- ** Constraint synonyms
            , HilbertSpace, SimpleSpace
            , Num', Num'', Num'''
            , Fractional', Fractional''
            , RealFrac', RealFloat'
            -- ** Misc
            , relaxNorm, transformNorm, transformVariance
            , findNormalLength, normalLength
            , summandSpaceNorms, sumSubspaceNorms
            , sharedNormSpanningSystem, sharedSeminormSpanningSystem
            ) where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted
import Math.VectorSpace.Docile

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

import Numeric.IEEE

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
spanNorm :: LSpace v => [DualVector v] -> Seminorm v
spanNorm dvs = Norm . LinearFunction $ \v -> sumV [dv ^* (dv<.>^v) | dv <- dvs]

spanVariance :: LSpace v => [v] -> Variance v
spanVariance = spanNorm

-- | Modify a norm in such a way that the given vectors lie within its unit ball.
--   (Not /optimally/ – the unit ball may be bigger than necessary.)
relaxNorm :: SimpleSpace v => Norm v -> [v] -> Norm v
relaxNorm me = \vs -> dualNorm . spanVariance $ vs' ++ vs
 where vs' = normSpanningSystem' me

-- | Scale the result of a norm with the absolute of the given number.
-- 
-- @
-- scaleNorm μ n |$| v = abs μ * (n|$|v)
-- @
-- 
-- Equivalently, this scales the norm's unit ball by the reciprocal of that factor.
scaleNorm :: LSpace v => Scalar v -> Norm v -> Norm v
scaleNorm μ (Norm n) = Norm $ μ^2 *^ n

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
instance LSpace v => Semigroup (Norm v) where
  Norm m <> Norm n = Norm $ m^+^n
-- | @mempty|$|v ≡ 0@
instance LSpace v => Monoid (Seminorm v) where
  mempty = Norm zeroV
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

transformNorm :: (LSpace v, LSpace w, Scalar v~Scalar w) => (v+>w) -> Norm w -> Norm v
transformNorm f (Norm m) = Norm . arr $ (adjoint $ f) . (fmap m $ f)

transformVariance :: (LSpace v, LSpace w, Scalar v~Scalar w)
                        => (v+>w) -> Variance v -> Variance w
transformVariance f (Norm m) = Norm . arr $ f . (fmap m $ adjoint $ f)

infixl 6 ^%
(^%) :: (LSpace v, Floating (Scalar v)) => v -> Norm v -> v
v ^% Norm m = v ^/ sqrt ((m$v)<.>^v)

-- | The unique positive number whose norm is 1 (if the norm is not constant zero).
findNormalLength :: RealFrac' s => Norm s -> Maybe s
findNormalLength (Norm m) = case m $ 1 of
   o | o > 0      -> Just . sqrt $ recip o
     | otherwise  -> Nothing

-- | Unsafe version of 'findNormalLength', only works reliable if the norm
--   is actually positive definite.
normalLength :: RealFrac' s => Norm s -> s
normalLength (Norm m) = case m $ 1 of
   o | o >= 0     -> sqrt $ recip o
     | o < 0      -> error "Norm fails to be positive semidefinite."
     | otherwise  -> error "Norm yields NaN."

infixr 0 <$|, |$|
-- | “Partially apply” a norm, yielding a dual vector
--   (i.e. a linear form that accepts the second argument of the scalar product).
-- 
-- @
-- ('euclideanNorm' '<$|' v) '<.>^' w  ≡  v '<.>' w
-- @
(<$|) :: LSpace v => Norm v -> v -> DualVector v
Norm m <$| v = m $ v

-- | The squared norm. More efficient than '|$|' because that needs to take
--   the square root.
normSq :: LSpace v => Seminorm v -> v -> Scalar v
normSq (Norm m) v = (m$v)<.>^v

-- | Use a 'Norm' to measure the length / norm of a vector.
-- 
-- @
-- 'euclideanNorm' |$| v  ≡  √(v '<.>' v)
-- @
(|$|) :: (LSpace v, Floating (Scalar v)) => Seminorm v -> v -> Scalar v
(|$|) m = sqrt . normSq m

-- | 'spanNorm' / 'spanVariance' are inefficient if the number of vectors
--   is similar to the dimension of the space, or even larger than it.
--   Use this function to optimise the underlying operator to a dense
--   matrix representation.
densifyNorm :: LSpace v => Norm v -> Norm v
densifyNorm (Norm m) = Norm . arr $ sampleLinearFunction $ m

data OrthonormalSystem v = OrthonormalSystem {
      orthonormalityNorm :: Norm v
    , orthonormalVectors :: [v]
    }

orthonormaliseFussily :: (LSpace v, RealFloat (Scalar v))
                           => Scalar v -> Norm v -> [v] -> [v]
orthonormaliseFussily fuss me = go []
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
      = orthogonalComplementProj' . map (id &&& (m$))



data Eigenvector v = Eigenvector {
      ev_Eigenvalue :: Scalar v -- ^ The estimated eigenvalue @λ@.
    , ev_Eigenvector :: v       -- ^ Normalised vector @v@ that gets mapped to a multiple, namely:
    , ev_FunctionApplied :: v   -- ^ @f $ v ≡ λ *^ v @.
    , ev_Deviation :: v         -- ^ Deviation of these two supposedly equivalent expressions.
    , ev_Badness :: Scalar v    -- ^ Squared norm of the deviation, normalised by the eigenvalue.
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
constructEigenSystem me@(Norm m) ε₀ f = iterate (
                                             sortBy (comparing $
                                               negate . abs . ev_Eigenvalue)
                                           . map asEV
                                           . orthonormaliseFussily (1/4) (Norm m)
                                           . newSys)
                                         . map (asEV . (^%me))
 where newSys [] = []
       newSys (Eigenvector λ v fv dv ε : evs)
         | ε>ε₀       = case newSys evs of
                         []     -> [fv^/λ, dv^*(sqrt $ λ^2/ε)]
                         vn:vns -> fv^/λ : vn : dv^*(sqrt $ λ^2/ε) : vns
         | ε>=0       = v : newSys evs
         | otherwise  = newSys evs
       asEV v = Eigenvector λ v fv dv ε
        where λ = v'<.>^fv
              ε = normSq me dv / (λ^2 + ε₀)
              fv = f $ v
              dv = v^*λ ^-^ fv
              v' = m $ v


finishEigenSystem :: (LSpace v, RealFloat (Scalar v))
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
              
              (μ₀₀,μ₀₁) = normalized ( λ₀ - λ₁
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
             _ -> let evss' = constructEigenSystem me fpε (arr f)
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
normSpanningSystem me@(Norm m)
     = catMaybes . map snd . orthonormaliseDuals 0
         . map (id&&&(m$)) $ normSpanningSystem' me

normSpanningSystem' :: (FiniteDimensional v, IEEE (Scalar v))
               => Seminorm v -> [v]
normSpanningSystem' me = orthonormaliseFussily 0 me $ enumerateSubBasis entireBasis


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
sharedNormSpanningSystem :: SimpleSpace v
               => Norm v -> Seminorm v -> [(DualVector v, Scalar v)]
sharedNormSpanningSystem nn@(Norm n) nm = first (n$) <$> sharedNormSpanningSystem' nn nm

sharedNormSpanningSystem' :: SimpleSpace v
               => Norm v -> Seminorm v -> [(v, Scalar v)]
sharedNormSpanningSystem' nn@(Norm n) (Norm m)
           = sep =<< roughEigenSystem nn (arr n' . arr m)
 where sep (Eigenvector λ v λv _ _)
         | λ>0        = [(λv^/λ, sqrt λ)]
         | μ<-(m$v)<.>^v
         , μ >= 0     = [(v    , sqrt μ)]
         | otherwise  = []
       Norm n' = dualNorm nn

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
sharedSeminormSpanningSystem :: SimpleSpace v
               => Seminorm v -> Seminorm v -> [(DualVector v, Maybe (Scalar v))]
sharedSeminormSpanningSystem nn@(Norm n) nm@(Norm m)
             = (second Just <$> lhsFullrank)
            ++ ((, Nothing) <$> normSpanningSystem rhsSolo)
 where lhsFullrank = sharedNormSpanningSystem nn nm
       Norm lhsFrApprox = spanNorm [dv^*η | (dv,η)<-lhsFullrank]
       rhsSolo = densifyNorm . Norm $ m^-^lhsFrApprox


-- | Interpret a variance as a covariance between two subspaces, and
--   normalise it by the variance on @u@. The result is effectively
--   the linear regression coefficient of a simple regression of the vectors
--   spanning the variance.
dependence :: (SimpleSpace u, SimpleSpace v, Scalar u~Scalar v)
                => Variance (u,v) -> (u+>v)
dependence (Norm m) = fmap ( snd . m . (id&&&zeroV) )
      $ pseudoInverse (arr $ fst . m . (id&&&zeroV))


summandSpaceNorms :: (SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v)
                       => Norm (u,v) -> (Norm u, Norm v)
summandSpaceNorms nuv = ( densifyNorm $ spanNorm (fst<$>spanSys)
                        , densifyNorm $ spanNorm (snd<$>spanSys) )
 where spanSys = normSpanningSystem nuv

sumSubspaceNorms :: (LSpace u, LSpace v, Scalar u~Scalar v)
                         => Norm u -> Norm v -> Norm (u,v)
sumSubspaceNorms (Norm nu) (Norm nv) = Norm $ nu *** nv





instance (SimpleSpace v, Show (DualVector v)) => Show (Norm v) where
  showsPrec p n = showParen (p>9) $ ("spanNorm "++) . shows (normSpanningSystem n)
