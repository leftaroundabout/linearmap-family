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

import Numeric.LinearAlgebra.Static.Orphans
import Numeric.LinearAlgebra.Static as HMatS hiding ((===), (<.>), ℝ)
import qualified Numeric.LinearAlgebra as HMat

import Data.AffineSpace
import Linear.V3
import Linear.V4
import Data.Basis
import Data.Coerce
import Math.LinearMap.Category
import Math.LinearMap.Coercion
import Math.VectorSpace.DimensionAware (toArray, fromArray, unsafeFromArray)
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
    , testProperty "Linearity"
       $ \f μ v w -> (f $ μ*^v ^+^ w) ≈≈≈ μ*^(f $ v) ^+^ (f $ w)
        `with`(f :: R 67+>R 86)
    , testProperty "Linear space of maps"
       $ \μ f g v -> (μ*^f ^+^ g $ v) ≈≈≈ μ*^(f $ v) ^+^ (g $ v)
        `with`(f :: R 67+>R 86)
    , testProperty "Composition"
       $ \f g v -> (f . g $ v) ≈≈≈ (f $ g $ v)
        `with`( f :: R 21+>R 20
              , v :: R 22 )
    , testProperty "Composition associativity"
       $ \f g h -> (f . g) . h ≈≈≈ f . (g . h)
        `with`( f :: R 8+>R 9
              , h :: R 6+>R 7 )
    ]
   ]


instance ∀ n . KnownNat n => Arbitrary (R n) where
  arbitrary = HMatS.fromList <$> vectorOf n arbitrary
   where n = fromIntegral $ natVal (Proxy @n)
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

infix 4 ≈≈≈
(≈≈≈) :: (InnerSpace v, Show v, Eq v, RealFrac (Scalar v))
            => v -> v -> QC.Property
v≈≈≈w
 | magnitudeSq (v^-^w) < (magnitudeSq v + magnitudeSq w)*1e-8   = QC.property True
 | otherwise                                                    = v===w

infix 0 `with`
with :: a -> b -> a
with = const

fzipTensor :: ( TensorSpace u, TensorSpace v, TensorSpace w
               , Scalar v ~ Scalar u, Scalar w ~ Scalar u )
      => (u ⊗ v, u ⊗ w) -+> (u ⊗ (v,w))
fzipTensor = fzipTensorWith-+$>id
