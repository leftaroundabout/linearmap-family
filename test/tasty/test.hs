-- |
-- Module      : test
-- Copyright   : (c) Justus Sagemüller 2021
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
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies         #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Data.AffineSpace
import Linear.V3
import Linear.V4
import Data.Basis
import Data.Coerce
import Math.LinearMap.Category
import Math.VectorSpace.DimensionAware (toArray, fromArray, unsafeFromArray)
import Math.Manifold.Core.Types
import Math.Manifold.Core.PseudoAffine

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC

import qualified Data.Vector.Unboxed as UArr


newtype ℝ⁴ = ℝ⁴ { getℝ⁴ :: V4 ℝ }
 deriving (Eq, Show)

copyNewtypeInstances [t| ℝ⁴ |]
   [ ''AdditiveGroup, ''AffineSpace, ''VectorSpace
   , ''Semimanifold, ''PseudoAffine
   , ''DimensionAware, ''Dimensional, ''TensorSpace, ''LinearSpace
   , ''FiniteDimensional, ''SemiInner, ''InnerSpace ]

newtype H¹ℝ⁴ a = H¹ℝ⁴ { getH¹ℝ⁴ :: ((a,a),(a,a)) }
 deriving (Eq, Show)

copyNewtypeInstances [t| ∀ a
          . (RealFloat' a, FiniteDimensional a, SemiInner a) => H¹ℝ⁴ a |]
   [ ''AdditiveGroup, ''AffineSpace, ''VectorSpace
   , ''Semimanifold, ''PseudoAffine
   , ''DimensionAware, ''Dimensional, ''TensorSpace, ''LinearSpace
   , ''FiniteDimensional, ''SemiInner ]

derivative₄ :: H¹ℝ⁴ ℝ -> ℝ⁴
derivative₄ (H¹ℝ⁴ ((w,x),(y,z))) = ℝ⁴ (V4 z w x y) ^-^ ℝ⁴ (V4 x y z w)

instance InnerSpace (H¹ℝ⁴ ℝ) where
  H¹ℝ⁴ v <.> H¹ℝ⁴ w = v<.>w + derivative₄ (H¹ℝ⁴ v)<.>derivative₄ (H¹ℝ⁴ w)

instance Arbitrary ℝ⁴ where
  arbitrary = ℝ⁴ <$> do
      V4 <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary w => Arbitrary (Tensor ℝ ℝ⁴ w) where
  arbitrary = Tensor <$> do
      V4 <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary


newtype ℝ⁵ a = ℝ⁵ { getℝ⁵ :: [ℝ] }
 deriving (Eq, Show)

instance AdditiveGroup (ℝ⁵ a) where
  zeroV = ℝ⁵ $ replicate 5 0
  ℝ⁵ v ^+^ ℝ⁵ w = ℝ⁵ $ zipWith (+) v w
  negateV (ℝ⁵ v)  = ℝ⁵ $ map negate v

instance VectorSpace (ℝ⁵ a) where
  type Scalar (ℝ⁵ a) = ℝ
  μ*^ℝ⁵ v = ℝ⁵ $ map (μ*) v

instance InnerSpace (ℝ⁵ a) where
  ℝ⁵ v <.> ℝ⁵ w = sum $ zipWith (*) v w

type Z5 = Z3+Z2
type Z3 = Z2+()
type Z2 = ()+()

instance Num a => HasBasis (ℝ⁵ a) where
  type Basis (ℝ⁵ a) = Z5
  basisValue (Left (Left (Left  ()))) = ℝ⁵ [1,0,0,0,0]
  basisValue (Left (Left (Right ()))) = ℝ⁵ [0,1,0,0,0]
  basisValue (Left (Right     ()   )) = ℝ⁵ [0,0,1,0,0]
  basisValue (Right (Left     ()   )) = ℝ⁵ [0,0,0,1,0]
  basisValue (Right (Right    ()   )) = ℝ⁵ [0,0,0,0,1]
  decompose (ℝ⁵ [a,b,c,d,e]) = 
   [ (Left (Left (Left  ())), a)
   , (Left (Left (Right ())), b)
   , (Left (Right     ()   ), c)
   , (Right (Left     ()   ), d)
   , (Right (Right    ()   ), e) ]
  decompose' (ℝ⁵ [a,b,c,d,e]) n = case n of
   Left (Left (Left  ())) ->  a
   Left (Left (Right ())) ->  b
   Left (Right     ()   ) ->  c
   Right (Left     ()   ) ->  d
   Right (Right    ()   ) ->  e

instance Arbitrary (ℝ⁵ a) where
  arbitrary = ℝ⁵ <$> QC.vectorOf 5 arbitrary

makeFiniteDimensionalFromBasis [t| ∀ a . Num a => ℝ⁵ a |]

newtype H¹ℝ⁵ = H¹ℝ⁵ { getH¹ℝ⁵ :: ℝ⁵ Int }
 deriving newtype (Eq, Show, AdditiveGroup, VectorSpace, HasBasis, Arbitrary)

makeFiniteDimensionalFromBasis [t| H¹ℝ⁵ |]

derivative₅ :: H¹ℝ⁵ -> ℝ⁵ Int
derivative₅ (H¹ℝ⁵ (ℝ⁵ (x₀:xs))) = ℝ⁵ (x₀:xs) ^-^ ℝ⁵ (xs++[x₀])

instance InnerSpace H¹ℝ⁵ where
  H¹ℝ⁵ v <.> H¹ℝ⁵ w = v<.>w + derivative₅ (H¹ℝ⁵ v)<.>derivative₅ (H¹ℝ⁵ w)

instance Arbitrary (V4 ℝ) where
  arbitrary = V4<$>arbitrary<*>arbitrary<*>arbitrary<*>arbitrary



main :: IO ()
main = do
  defaultMain $ testGroup "Tests"
   [ testGroup "Euclidean space"
    [ testProperty "co-Riesz inversion"
     $ \v -> (arr coRiesz\$coRiesz-+$>v) === (v :: V4 ℝ)
    , testProperty "Random operator inversion"
     $ \f v -> not (isSingular f)
              ==> (f \$ (f :: V4 ℝ+>V4 ℝ) $ v) ≈≈≈ v
    ]
   , testGroup "Basis-derived space"
    [ testProperty "Semimanifold addition"
     $ \v w -> v.+~^w === (v^+^w :: ℝ⁵ Int)
    , testProperty "Riesz representation, orthonormal basis"
     $ \v -> (riesz-+$>coRiesz-+$>v) === (v :: ℝ⁵ Int)
    , testProperty "Riesz representation, non-orthonormal basis"
     $ \v -> (riesz-+$>coRiesz-+$>v) ≈≈≈ (v :: H¹ℝ⁵)
    ]
   , testGroup "Newtype-derived space"
    [ testProperty "Addition"
     $ \v w -> ℝ⁴ v^+^ℝ⁴ w === ℝ⁴ (v^+^w)
    , testProperty "Riesz representation, orthonormal basis"
     $ \v -> (riesz-+$>coRiesz-+$>ℝ⁴ v) === ℝ⁴ v
    , testProperty "Riesz is trivial in orthonormal basis"
     $ \v -> (riesz-+$>AbstractDualVector v) ≈≈≈ ℝ⁴ v
    , testProperty "Riesz representation, non-orthonormal basis"
     $ \v -> (riesz-+$>coRiesz-+$>H¹ℝ⁴ v) ≈≈≈ (H¹ℝ⁴ v :: H¹ℝ⁴ Double)
    , testProperty "Riesz nontriviality in general case"
     . QC.expectFailure
     $ \v -> (riesz-+$>AbstractDualVector v) ≈≈≈ (H¹ℝ⁴ v :: H¹ℝ⁴ Double)
    ]
   , testGroup "Reading from arrays"
    [ testProperty "Scalars"
     $ \x -> fromArray (uar [x :: ℝ]) === Just x
    , testProperty "Pairs"
     $ \x y -> fromArray (uar [x,y :: ℝ]) === Just (x,y)
    , testProperty "Nested pairs"
     $ \x y ξ υ -> fromArray (uar [x,y,ξ,υ :: ℝ]) === Just ((x,y),(ξ,υ))
    , testProperty "ℝ³"
     $ \x y z -> fromArray (uar [x,y,z :: ℝ]) === Just (V3 x y z)
    , testProperty "Tensors: (ℝ,ℝ)⊗ℝ³"
     $ \x y z ξ υ ζ -> fromArray (uar [x,y,z
                                      ,ξ,υ,ζ :: ℝ])
                          === Just (coerce ( V3 x y z
                                           , V3 ξ υ ζ ) :: (ℝ,ℝ)⊗V3 ℝ)
    , testProperty "Tensors: ℝ³⊗(ℝ,ℝ)"
     $ \x y z ξ υ ζ -> fromArray (uar [x,ξ
                                      ,y,υ
                                      ,z,ζ :: ℝ])
                          === Just (coerce (V3 (x,ξ)
                                               (y,υ)
                                               (z,ζ)) :: V3 ℝ⊗(ℝ,ℝ))
    , testProperty "Tensors: (ℝ,ℝ)⊗(ℝ,ℝ)⊗(ℝ,ℝ)"
     $ \a b c d e f g h -> fromArray (uar [a,b,c,d,e,f,g,h :: ℝ])
                          == Just (coerce (((a,b),(c,d)),((e,f),(g,h)))
                                         :: (ℝ,ℝ)⊗(ℝ,ℝ)⊗(ℝ,ℝ))
    , testProperty "Linear functions: (ℝ,ℝ)-+>ℝ³"
     $ \xx xy yx yy zx zy x y
          -> (unsafeFromArray (uar [xx,yx,zx
                                   ,xy,yy,zy])
               -+$> (unsafeFromArray (uar [x,y]) :: (ℝ,ℝ)))
               === (unsafeFromArray
                      (uar [ xx*x + xy*y
                           , yx*x + yy*y
                           , zx*x + zy*y ]) :: V3 ℝ)
    , testProperty "Linear functions: ℝ³-+>(ℝ,ℝ)"
     $ \xx xy xz yx yy yz x y z
          -> (unsafeFromArray (uar [xx,yx
                                   ,xy,yy
                                   ,xz,yz])
               -+$> (unsafeFromArray (uar [x,y,z]) :: V3 ℝ))
               === (unsafeFromArray
                      (uar [ xx*x + xy*y + xz*z
                           , yx*x + yy*y + yz*z ]) :: (ℝ,ℝ))
                              -- N.B. this test is sensitive to the computation
                              -- order, e.g. it fails with xy*y + xx*x + xz*z due to
                              -- floating-point non-associativity and the exact ===.
    ]
   , testGroup "Array conversion"
    $ let arrayRoundTrip :: ∀ v n . (n`Dimensional`v, Scalar v ~ ℝ, Eq v, Show v)
                      => v -> QC.Property
          arrayRoundTrip v = fromArray (toArray v :: UArr.Vector ℝ) === Just v
      in [ testProperty "ℝ" $ arrayRoundTrip @ℝ
         , testProperty "(ℝ,ℝ)" $ arrayRoundTrip @(ℝ,ℝ)
         , testProperty "ℝ³" $ arrayRoundTrip @(V3 ℝ)
         , testProperty "ℝ⁴ (newtype-derived)" $ arrayRoundTrip @ℝ⁴
         , testProperty "ℝ⁵ (basis-derived)" $ arrayRoundTrip @(ℝ⁵ Int)
         , testProperty "ℝ³⊗(ℝ,ℝ)" $ arrayRoundTrip @(V3 ℝ⊗(ℝ,ℝ))
         , testProperty "(ℝ,ℝ)⊗ℝ³" $ arrayRoundTrip @((ℝ,ℝ)⊗V3 ℝ)
         , testProperty "ℝ³⊗ℝ³⊗ℝ³" $ arrayRoundTrip @(V3 ℝ⊗V3 ℝ⊗V3 ℝ)
         , testProperty "ℝ³+>ℝ³" $ arrayRoundTrip @(V3 ℝ+>V3 ℝ)
         , testProperty "ℝ³⊗ℝ⁴⊗ℝ⁵" $ arrayRoundTrip @(V3 ℝ⊗ℝ⁴⊗ℝ⁵ Int)
         ]
   ]


(≈≈≈) :: (InnerSpace v, Show v, Eq v, RealFrac (Scalar v))
            => v -> v -> QC.Property
v≈≈≈w
 | magnitudeSq (v^-^w) < (magnitudeSq v + magnitudeSq w)*1e-8   = QC.property True
 | otherwise                                                    = v===w

isSingular :: ∀ v n . (n`Dimensional`v, Scalar v ~ ℝ)
             => (v +> v) -> Bool
isSingular _ = undefined

uar :: UArr.Unbox a => [a] -> UArr.Vector a
uar = UArr.fromList

instance QC.Arbitrary s => QC.Arbitrary (V3 s) where
  arbitrary = V3 <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary
