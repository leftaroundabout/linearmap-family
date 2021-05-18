-- |
-- Module      : test
-- Copyright   : (c) Justus Sagemüller 2021
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE UnicodeSyntax       #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

import qualified Prelude as Hask
import Control.Category.Constrained.Prelude
import Control.Arrow.Constrained

import Math.LinearMap.Category

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck as QC


main :: IO ()
main = do
  defaultMain $ testGroup "Tests"
   [
   ]

