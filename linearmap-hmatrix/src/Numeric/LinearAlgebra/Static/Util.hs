{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE CPP                    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UnicodeSyntax          #-}

module Numeric.LinearAlgebra.Static.Util where

-- base
import GHC.TypeLits (KnownNat, natVal)
import GHC.Stack (HasCallStack)
import Data.Proxy (Proxy(..))
import Data.Maybe (fromJust)

-- hmatrix
import Numeric.LinearAlgebra.Static as HMatS
import qualified Numeric.LinearAlgebra as HMat

-- vector
import qualified Data.Vector.Storable as ArS

-- tagged
#if !MIN_VERSION_manifolds_core(0,6,0)
import Data.Tagged (Tagged(..))
#endif


natVal' :: ∀ n t . (KnownNat n, Num t) => t
natVal' = fromInteger $ natVal @n Proxy

generateV :: ∀ n . KnownNat n => (Int -> ℝ) -> R n
generateV = fromJust . create . ArS.generate (natVal' @n)

unsafeCreate :: ∀ n . (KnownNat n, HasCallStack) => ArS.Vector ℝ -> R n
unsafeCreate ar
  | nar==n     = fromJust $ create ar
  | otherwise  = error $ "Incorrect size "++show nar++" for dimension "++show n
 where n = natVal' @n
       nar = ArS.length ar

unsafeCreateMat :: ∀ n m . (KnownNat n, KnownNat m, HasCallStack)
                     => HMat.Matrix ℝ -> L n m
unsafeCreateMat mat
  | nmat==n, mmat==m  = fromJust $ create mat
  | otherwise         = error $ "Incorrect size "++show nmat++"×"++show mmat
                               ++" for dimension "++show n++"×"++show m
 where n = natVal' @n
       m = natVal' @m
       nmat = HMat.rows mat
       mmat = HMat.cols mat

unsafeFromRows :: ∀ m n . (KnownNat m, KnownNat n, HasCallStack) => [R n] -> L m n
unsafeFromRows rs = withRows rs  -- unsafeCoerce
                                (fromJust . exactDims)

unsafeFromCols :: ∀ m n . (KnownNat m, KnownNat n, HasCallStack) => [R m] -> L m n
unsafeFromCols rs = withColumns rs  -- unsafeCoerce
                                  (fromJust . exactDims)

generateCols :: ∀ m n . (KnownNat m, KnownNat n, HasCallStack)
       => (Int -> R m) -> L m n
generateCols f = unsafeFromCols $ f <$> [0 .. natVal' @n - 1]

