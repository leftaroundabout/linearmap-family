-- |
-- Module      : test
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Math.LinearMap.Category
import Math.Manifold.Core.Types
import Math.Manifold.Core.PseudoAffine

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC



newtype ℝ⁴⁷ = ℝ⁴⁷ { getℝ⁴⁷ :: [ℝ] }
 deriving (Eq, Show)

instance AdditiveGroup ℝ⁴⁷ where
  zeroV = ℝ⁴⁷ $ replicate 47 0
  ℝ⁴⁷ v ^+^ ℝ⁴⁷ w = ℝ⁴⁷ $ zipWith (+) v w
  negateV (ℝ⁴⁷ v)  = ℝ⁴⁷ $ map negate v

instance Arbitrary ℝ⁴⁷ where
  arbitrary = ℝ⁴⁷ <$> QC.vectorOf 47 arbitrary

makeTensorSpaceFromBasis [t| ℝ⁴⁷ |]

main :: IO ()
main = do
  defaultMain $ testGroup "Tests"
   [ testGroup "Basis-derived space"
    [ testProperty "Semimanifold addition"
     $ \v w -> v.+~^w === (v^+^w :: ℝ⁴⁷)
    ]
   ]

