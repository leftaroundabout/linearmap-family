-- |
-- Module      : tasty
-- Copyright   : (c) Justus Sagemüller 2023
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE UndecidableInstances       #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Math.LinearMap.Category.Backend.HMatrix
import Numeric.LinearAlgebra.Static as HMatS hiding ((===), (<.>), ℝ)
import qualified Numeric.LinearAlgebra as HMat

import Data.AffineSpace
import Linear.V3
import Linear.V4
import Data.Basis
import Data.Coerce
import Math.LinearMap.Category
import Math.LinearMap.Coercion
import Math.VectorSpace.DimensionAware (toArray, fromArray, unsafeFromArray, withDimension)
import Math.Manifold.Core.Types
import Math.Manifold.Core.PseudoAffine

import GHC.TypeLits (KnownNat, natVal)
import Data.Proxy (Proxy(..))
import Data.Function (on)

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC

import qualified Data.Vector.Unboxed as UArr



main :: IO ()
main = do
  defaultMain $ testGroup "Tests"
   [ testGroup "Vector-space basics"
    [ testProperty "Addition associativity"
       $ \v w x -> (v^+^w)^+^x ≈≈≈ v^+^(w^+^x)
        `with`[v, w, x :: R 27]
    , testProperty "Addition commutativity"
       $ \v w -> v^+^w === w^+^v
        `with`[v, w :: R 39]
    , testProperty "Scalar distributivity"
       $ \μ v w -> μ*^(v^+^w) ≈≈≈ μ*^v ^+^ μ*^w
        `with`[v, w :: R 92]
    , testProperty "Inner product bilinearity"
       $ \μ u v ν w x -> (μ*^u ^+^ v)<.>(ν*^w ^+^ x)
                      ≈≈≈ μ*ν*(u<.>w) + μ*(u<.>x) + ν*(v<.>w) + v<.>x
        `with`[u, v, w, x :: R 512]
    ]
   , testGroup "Tensors"
    [ testProperty "Tensor product associativity"
       $ \v w x -> v⊗(w⊗x) ≈≈≈ coerce ((v⊗w)⊗x)
        `with`(v :: R 37, w :: R 38, x :: R 39)
    , testProperty "Fmapping identity"
       $ \t -> (fmap id -+$> t) === t
        `with`(t :: R 97⊗R 43)
    , testProperty "Fmapping composition"
       $ \t f g -> (fmap (applyLinear-+$>g . f) $ t)
                       ≈≈≈ (fmap (applyLinear-+$>g) $ fmap (applyLinear-+$>f) $ t)
        `with`(t :: R 97⊗R 43, f :: R 43+>R 44, g :: R 44+> R 45)
    , testProperty "Fmapping pair tensor"
       $ \t@(Tensor (t₀,t₁)) f
          -> let fl = applyLinear-+$>f
              in (fmap fl $ t) ≈≈≈ Tensor (fmap fl $ t₀, fmap fl $ t₁)
                   `with`(t :: (R 25,R 26)⊗R 43, f :: R 43+>R 44)
    , testProperty "Fmapping pair-pair tensor"
       $ \t@(Tensor (t₀,t₁)) f
          -> let fl = applyLinear-+$>f
              in (fmap fl $ t) ≈≈≈ Tensor (fmap fl $ t₀, fmap fl $ t₁)
                   `with`(t :: (R 25,R 26)⊗(R 3,R 4), f :: (R 3,R 4)+>R 55)
    , testProperty "Fmapping pair-valued function"
       $ \t f
          -> let fl = applyLinear-+$>f
              in (fmap fl $ t) ≈≈≈ (fzipTensor-+$>( fmap (fst.(applyLinear-+$>f))-+$>t
                                                  , fmap (snd.(applyLinear-+$>f))-+$>t ))
                   `with`(t :: R 25⊗R 7, f :: R 7+>(R 55, R 49))
    ]
   , testGroup "Linear maps"
    [ testProperty "Identity"
       $ \v -> (linearId $ v :: R 7968) === v
    , testProperty "Identity for pairs"
       $ \v w -> (linearId $ (v,w)) === (v,w)
        `with`(v :: R 87, w :: R 92)
    , testProperty "Linearity"
       $ \f μ v w -> (f $ μ*^v ^+^ w) ≈≈≈ μ*^(f $ v) ^+^ (f $ w)
        `with`(f :: R 67+>R 86)
    , testProperty "Linear space of maps"
       $ \μ f g v -> (μ*^f ^+^ g $ v) ≈≈≈ μ*^(f $ v) ^+^ (g $ v)
        `with`(f :: R 67+>R 86)
    , testProperty "fst projection"
       $ \x y -> ((fst :: (R 2, R 3)+>R 2) $ (x,y)) ≈≈≈ x
    , testProperty "Identity composition on pairs"
       $ \x y -> (id . linearId @(R 2, R 3) $ (x,y)) ≈≈≈ (x,y)
    , testProperty "Composition"
       $ \f g v -> (f . g $ v) ≈≈≈ (f $ g $ v)
        `with`( f :: R 21+>R 20
              , v :: R 22 )
    , testProperty "Composition associativity"
       $ \f g h -> (f . g) . h ≈≈≈ f . (g . h)
        `with`( f :: R 8+>R 9
              , h :: R 6+>R 7 )
    , testProperty "Parallel / blocks"
       $ \f g x y -> (f *** g $ (x,y)) ≈≈≈ (f $ x, g $ y)
        `with`( f :: R 46+>R 243
              , g :: R 98+>R 123 )
    , testProperty "Duplicates"
       $ \x -> ((id &&& (id :: R 9+>R 9)) $ x)
                  ≈≈≈ (x, x)
    , testProperty "Identity composition for pairs"
       $ \x y -> (id . linearId @(R 3, R 4) $ (x,y))
                  ≈≈≈ (x, y)
    , testProperty "Duplicate add"
       $ \x -> ((fst^+^snd) . (id &&& (id :: R 9+>R 9)) $ x)
                  ≈≈≈ 2 *^ x
    , testProperty "Fanout and add"
       $ \f g x -> ((fst^+^snd) . (f &&& g) $ x)
                  ≈≈≈ (f $ x) ^+^ (g $ x)
        `with`[f, g :: R 9+>R 9]
    , testProperty "Parallel composition"
       $ \f g h i x y -> ((f *** g) . (h *** i) $ (x,y))
                         ≈≈≈ (f . h *** g . i $ (x,y))
        `with`( f :: R 46+>R 243
              , g :: R 98+>R 123
              , h :: R 102+>R 46
              , i :: R 78+>R 98 )
    ]
   , testGroup "HMatrix-based mappings between free spaces"
    [ testProperty "Conversion from general tensor-based to HMatrix-based linmap"
       $ \(f :: ((ℝ,ℝ),ℝ) +> (ℝ,(ℝ,ℝ))) v
            -> let fHM = linfunAsHMatrixImpl-+$>(applyLinear-+$>f) -- inefficient
               in (fromHMatrixImpl-+$>((applyLinear-+$>fHM)-+$>(asHMatrixImpl-+$>v)))
                     ≈≈≈ ((applyLinear-+$>f)-+$>v)
    , testProperty "Conversion from HMatrix-based to general tensor-based linmap"
       $ \(fHM :: HMatrixImpl ((ℝ,ℝ),ℝ) +> HMatrixImpl (ℝ,(ℝ,ℝ))) (v :: ((ℝ,ℝ),ℝ))
            -> let f = sampleLinearFunction-+$>(linfunFromHMatrixImpl-+$>fHM) -- inefficient
               in (fromHMatrixImpl-+$>((applyLinear-+$>fHM)-+$>(asHMatrixImpl-+$>v)))
                     ≈≈≈ ((applyLinear-+$>f)-+$>v)
    ]
   ]


precision :: Double -> Int
precision x = go 0
 where go i
         | i>100
            || abs (x - fromIntegral (round $ x * 10^^i) / 10^^i) < abs x / 1e9
                      = i
         | otherwise  = go (i+1)

instance ∀ n . KnownNat n => Arbitrary (R n) where
  arbitrary = HMatS.fromList <$> vectorOf n arbitrary
   where n = fromIntegral $ natVal (Proxy @n)
  shrink v  -- uniformly strip away decimals from each entry
    | shrunk==v   = []
    | otherwise   = [shrunk]
   where l = HMat.toList $ extract v
         prc = maximum $ precision<$>l
         shrunk = HMatS.fromList
                   [ fromIntegral (round $ x * 10^^(prc-1)) / 10^^(prc-1)
                   | x <- l ]

instance ∀ n m r . (KnownNat n, KnownNat m, r~ℝ)
           => Arbitrary (LinearMap r (R n) (R m)) where
  arbitrary = LinearMap . HMatS.fromList
                <$> vectorOf (n*m) arbitrary
   where n = fromIntegral $ natVal (Proxy @n)
         m = fromIntegral $ natVal (Proxy @m)
instance ∀ n r u v . ( KnownNat n, r ~ ℝ
                     , TensorSpace u, TensorSpace v
                     , Scalar u ~ ℝ , Scalar v ~ ℝ
                     , Arbitrary (LinearMap r (R n) u)
                     , Arbitrary (LinearMap r (R n) v) )
           => Arbitrary (LinearMap r (R n) (u,v)) where
  arbitrary = (fromTensor $ ) <$> do
                curry (fzipTensor-+$>)
                 <$>((asTensor$) <$> arbitrary @(LinearMap r (R n) u))
                 <*>((asTensor$) <$> arbitrary @(LinearMap r (R n) v))
instance ∀ n v r . ( KnownNat n, TensorSpace v, r~ℝ, Scalar v~ℝ
                   , StaticDimensional v )
           => InnerSpace (Tensor r (R n) v) where
  (<.>) = dimensionIsStatic @v
    (\(Tensor f) (Tensor g)
       -> HMat.flatten (extract f) HMat.<.> HMat.flatten (extract g) )

instance ∀ n v r . ( KnownNat n, TensorSpace v, r~ℝ, Scalar v~ℝ
                   , StaticDimensional v )
           => Show (Tensor r (R n) v) where
  showsPrec p (Tensor t) = dimensionIsStatic @v (
    showParen (p>9) $ ("Tensor "++) . showsPrec 10 t )
instance ∀ n m r . (KnownNat n, KnownNat m, r~ℝ)
           => InnerSpace (LinearMap r (R n) (R m)) where
  LinearMap f<.>LinearMap g
      = HMat.flatten (extract f) HMat.<.> HMat.flatten (extract g)

instance ∀ v w r . ( LinearSpace v, StaticDimensional v, Scalar v ~ ℝ
                   , StaticDimensional w, Scalar w ~ ℝ
                   , r~ℝ )
           => Arbitrary (LinearMap r (HMatrixImpl v) (HMatrixImpl w)) where
  arbitrary = withDimension @v @Int (\n -> withDimension @w @Int (\m
                -> case dualSpaceWitness @v of
   DualSpaceWitness -> LinearMap . HMatS.fromList <$> vectorOf (n*m) arbitrary))

infix 4 ≈≈≈
(≈≈≈) :: (InnerSpace v, Show v, Eq v, RealFrac (Scalar v))
            => v -> v -> QC.Property
v≈≈≈w = QC.counterexample (show v ++ interpret res ++ show w) res
 where res = magnitudeSq (v^-^w) <= (magnitudeSq v + magnitudeSq w)*1e-8
       interpret True = " ≈ "
       interpret False = " ≠ "

infix 0 `with`
with :: a -> b -> a
with = const

fzipTensor :: ( TensorSpace u, TensorSpace v, TensorSpace w
               , Scalar v ~ Scalar u, Scalar w ~ Scalar u )
      => (u ⊗ v, u ⊗ w) -+> (u ⊗ (v,w))
fzipTensor = fzipTensorWith-+$>id
