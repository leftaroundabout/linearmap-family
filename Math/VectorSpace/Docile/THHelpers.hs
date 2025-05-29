-- |
-- Module      : Math.VectorSpace.Docile.THHelpers
-- Copyright   : (c) Justus Sagemüller 2025
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
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}

module Math.VectorSpace.Docile.THHelpers where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted
import Math.VectorSpace.Docile.Class

import Data.Tree (Tree(..), Forest)
import Data.List (sortBy, foldl', tails)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Ord (comparing)
import Data.List (maximumBy, unfoldr)
import qualified Data.Vector as Arr
import Data.Foldable (toList)
import Data.List (transpose)
import Data.Semigroup

import Data.VectorSpace
import Data.Basis

import Data.Void

import Prelude ()
import qualified Prelude as Hask

import Language.Haskell.TH
import THLego.Helpers (multiAppE)


import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained
import Control.Monad.Trans.State

import Linear ( V0(V0), V1(V1), V2(V2), V3(V3), V4(V4)
              , _x, _y, _z, _w, ex, ey, ez, ew )
import qualified Data.Vector.Unboxed as UArr
import Data.VectorSpace.Free
import Math.VectorSpace.ZeroDimensional
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import Control.Lens ((^.), Lens', lens, ReifiedLens', ReifiedLens(..))
import Data.Coerce

import Numeric.IEEE

import Data.CallStack



mkFreeFiniteDimensional :: Name -> Name -> Int -> Q [Dec]
mkFreeFiniteDimensional vTCstrName vECstrName dimens = do
  let 
      vTCstr :: Q Type
      vTCstr = pure . ConT $ vTCstrName
      
      vExprn xVars = multiAppE (ConE vECstrName) $ VarE<$>xVars
      vPatt xVars = ConP vECstrName [] $ VarP<$>xVars

      dim :: Q Type
      dim = pure . LitT . NumTyLit $ fromIntegral dimens
      newCVars :: Char -> Q [Name]
      newCVars sym = forM [0 .. dimens-1] $ newName . (sym:) . show

  scalarTVar <- (pure . VarT <$> newName "s" :: Q (Q Type))

  sequence [
    InstanceD Nothing <$> sequence
                           [ [t|Num' $scalarTVar|]
                           , [t|Eq $scalarTVar|]
                           , [t|LSpace $scalarTVar|] ]
                      <*> [t|FiniteDimensional ($vTCstr $scalarTVar)|]
                      <*> sequence
     [
     ]
   ]
      



recomposeMultiple :: FiniteDimensional w
              => SubBasis w -> Int -> [Scalar w] -> ([w], [Scalar w])
recomposeMultiple bw n dc
 | n<1        = ([], dc)
 | otherwise  = case recomposeSB bw dc of
           (w, dc') -> first (w:) $ recomposeMultiple bw (n-1) dc'
                                  
