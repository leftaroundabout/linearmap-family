-- |
-- Module      : TypeLevel.Maybe
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}

module TypeLevel.Maybe where

import GHC.TypeLits

type family ZipWith (f :: k -> l -> m) (a :: Maybe k) (b :: Maybe l) :: Maybe m where
  ZipWith f 'Nothing y = 'Nothing
  ZipWith f x 'Nothing = 'Nothing
  ZipWith f ('Just x) ('Just y) = 'Just (f x y)

type family ZipWithPlus (a :: Maybe Nat) (b :: Maybe Nat) :: Maybe Nat where
  ZipWithPlus 'Nothing y = 'Nothing
  ZipWithPlus x 'Nothing = 'Nothing
  ZipWithPlus ('Just x) ('Just y) = 'Just (x+y)
