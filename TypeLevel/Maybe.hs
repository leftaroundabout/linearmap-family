-- |
-- Module      : TypeLevel.Maybe
-- Copyright   : (c) Justus Sagemüller 2022
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE NoStarIsType               #-}

module TypeLevel.Maybe where

import Prelude.Singletons (SNum(..))
import Data.Singletons
import Data.Maybe.Singletons
import GHC.TypeLits
import GHC.TypeLits.Singletons

type family ZipWith (f :: k -> l -> m) (a :: Maybe k) (b :: Maybe l) :: Maybe m where
  ZipWith f 'Nothing y = 'Nothing
  ZipWith f x 'Nothing = 'Nothing
  ZipWith f ('Just x) ('Just y) = 'Just (f x y)

type family ZipWithPlus (a :: Maybe Nat) (b :: Maybe Nat) :: Maybe Nat where
  ZipWithPlus 'Nothing y = 'Nothing
  ZipWithPlus x 'Nothing = 'Nothing
  ZipWithPlus ('Just x) ('Just y) = 'Just (x+y)

type family ZipWithTimes (a :: Maybe Nat) (b :: Maybe Nat) :: Maybe Nat where
  ZipWithTimes 'Nothing y = 'Nothing
  ZipWithTimes x 'Nothing = 'Nothing
  ZipWithTimes ('Just x) ('Just y) = 'Just (x*y)

zipWithPlusCong :: ∀ a a' b b' r . (a ~ a', b ~ b')
    => ((ZipWithPlus a b ~ ZipWithPlus a' b') => r) -> r
zipWithPlusCong φ = φ

zipWithPlusSingI :: ∀ a b r . (SingI a, SingI b)
    => (SingI (ZipWithPlus a b) => r) -> r
zipWithPlusSingI φ = case (sing @a, sing @b) of
  (SNothing, _      ) -> φ
  (_      , SNothing) -> φ
  (SJust α, SJust β ) -> withKnownNat (α%+β) φ

zipWithTimesCong :: ∀ a a' b b' r . (a ~ a', b ~ b')
    => ((ZipWithTimes a b ~ ZipWithTimes a' b') => r) -> r
zipWithTimesCong φ = φ

zipWithTimesSingI :: ∀ a b r . (SingI a, SingI b)
    => (SingI (ZipWithTimes a b) => r) -> r
zipWithTimesSingI φ = case (sing @a, sing @b) of
  (SNothing, _      ) -> φ
  (_      , SNothing) -> φ
  (SJust α, SJust β ) -> withKnownNat (α%*β) φ

zipWithTimesAssoc :: ∀ a b c r . (SingI a, SingI b, SingI c)
    => ((ZipWithTimes a (ZipWithTimes b c) ~ ZipWithTimes (ZipWithTimes a b) c) => r)
           -> r
zipWithTimesAssoc φ = case (sing @a, sing @b, sing @c) of
  (SNothing, _     ,  _      ) -> φ
  (_      , SNothing, _      ) -> φ
  (_      , _      , SNothing) -> φ
  (SJust _, SJust _, SJust _ ) -> φ

zipWithTimesCommu :: ∀ a b r . (SingI a, SingI b)
    => ((ZipWithTimes a b ~ ZipWithTimes b a) => r)
           -> r
zipWithTimesCommu φ = case (sing @a, sing @b) of
  (SNothing, _      ) -> φ
  (_      , SNothing) -> φ
  (SJust _, SJust _ ) -> φ

