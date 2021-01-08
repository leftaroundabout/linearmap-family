-- |
-- Module      : Math.VectorSpace.Dual
-- Copyright   : (c) Justus Sagemüller 2020
-- License     : GPL v3
-- 
-- Maintainer  : (@) jsag $ hvl.no
-- Stability   : experimental
-- Portability : portable
-- 

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE UnicodeSyntax          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE KindSignatures         #-}

module Math.VectorSpace.Dual
       ( Dualness(..), Dual, DualityWitness(..), ValidDualness(..)
       , usingAnyDualness
        ) where



data Dualness = Vector | Functional

type family Dual (dn :: Dualness) where
  Dual Vector = Functional
  Dual Functional = Vector


data DualityWitness (dn :: Dualness) where
  DualityWitness :: (ValidDualness (Dual dn), Dual (Dual dn) ~ dn)
           => DualityWitness dn

data DualnessSingletons (dn :: Dualness) where
  VectorWitness :: DualnessSingletons Vector
  FunctionalWitness :: DualnessSingletons Functional

class ValidDualness (dn :: Dualness) where
  dualityWitness :: DualityWitness dn
  decideDualness :: DualnessSingletons dn
instance ValidDualness 'Vector where
  dualityWitness = DualityWitness
  decideDualness = VectorWitness
instance ValidDualness 'Functional where
  dualityWitness = DualityWitness
  decideDualness = FunctionalWitness

usingAnyDualness :: ∀ rc dn . ValidDualness dn
          => (rc 'Vector)
          -> (rc 'Functional)
          -> rc dn
usingAnyDualness vecCase ftnCase = case decideDualness @dn of
     VectorWitness -> vecCase
     FunctionalWitness -> ftnCase
