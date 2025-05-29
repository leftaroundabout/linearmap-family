-- |
-- Module      : Math.VectorSpace.Docile
-- Copyright   : (c) Justus Sagemüller 2016
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

module Math.VectorSpace.Docile
   ( module Math.VectorSpace.Docile.Class
   , SimpleSpace
   , HilbertSpace
   , RealFrac', RealFloat'
   , riesz, sRiesz, coRiesz
   , RieszDecomposable, rieszDecomposeShowsPrec, showsPrecAsRiesz
   , TensorDecomposable, tensorDecomposeShowsPrec
   , multiSplit
   , pseudoInverse
   , (\$)
   , (^)
   , (.<), (.⊗)
   , adjoint
   ) where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted
import Math.VectorSpace.Docile.Class
import Math.VectorSpace.Docile.THHelpers (mkFreeFiniteDimensional)

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

import Data.Kind (Type)

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


mkFreeFiniteDimensional ''V1 'V1 1
mkFreeFiniteDimensional ''V2 'V2 2
mkFreeFiniteDimensional ''V3 'V3 3
mkFreeFiniteDimensional ''V4 'V4 4



recomposeMultiple :: FiniteDimensional w
              => SubBasis w -> Int -> [Scalar w] -> ([w], [Scalar w])
recomposeMultiple bw n dc
 | n<1        = ([], dc)
 | otherwise  = case recomposeSB bw dc of
           (w, dc') -> first (w:) $ recomposeMultiple bw (n-1) dc'
                                  
deriving instance Show (SubBasis ℝ)
  
instance ∀ u v . ( FiniteDimensional u, FiniteDimensional v
                 , Scalar u ~ Scalar v )
            => FiniteDimensional (u,v) where
  data SubBasis (u,v) = TupleBasis !(SubBasis u) !(SubBasis v)
  entireBasis = TupleBasis entireBasis entireBasis
  enumerateSubBasis (TupleBasis bu bv)
       = ((,zeroV)<$>enumerateSubBasis bu) ++ ((zeroV,)<$>enumerateSubBasis bv)
  subbasisDimension (TupleBasis bu bv) = subbasisDimension bu + subbasisDimension bv
  decomposeLinMap = dclm dualSpaceWitness dualSpaceWitness dualSpaceWitness
   where dclm :: ∀ w . (LinearSpace w, Scalar w ~ Scalar u)
                    => DualSpaceWitness u -> DualSpaceWitness v -> DualSpaceWitness w
                          -> ((u,v)+>w) -> (SubBasis (u,v), DList w)
         dclm DualSpaceWitness DualSpaceWitness DualSpaceWitness (LinearMap (fu, fv))
          = case (decomposeLinMap (asLinearMap$fu), decomposeLinMap (asLinearMap$fv)) of
             ((bu, du), (bv, dv)) -> (TupleBasis bu bv, du . dv)
  decomposeLinMapWithin = dclm dualSpaceWitness dualSpaceWitness dualSpaceWitness
   where dclm :: ∀ w . (LinearSpace w, Scalar w ~ Scalar u)
                    => DualSpaceWitness u -> DualSpaceWitness v -> DualSpaceWitness w
                          -> SubBasis (u,v) -> ((u,v)+>w)
                            -> Either (SubBasis (u,v), DList w) (DList w)
         dclm DualSpaceWitness DualSpaceWitness DualSpaceWitness
                  (TupleBasis bu bv) (LinearMap (fu, fv))
          = case ( decomposeLinMapWithin bu (asLinearMap$fu)
                 , decomposeLinMapWithin bv (asLinearMap$fv) ) of
            (Left (bu', du), Left (bv', dv)) -> Left (TupleBasis bu' bv', du . dv)
            (Left (bu', du), Right dv) -> Left (TupleBasis bu' bv, du . dv)
            (Right du, Left (bv', dv)) -> Left (TupleBasis bu bv', du . dv)
            (Right du, Right dv) -> Right $ du . dv
  recomposeSB (TupleBasis bu bv) coefs = case recomposeSB bu coefs of
                        (u, coefs') -> case recomposeSB bv coefs' of
                         (v, coefs'') -> ((u,v), coefs'')
  recomposeSBTensor (TupleBasis bu bv) bw cs = case recomposeSBTensor bu bw cs of
            (tuw, cs') -> case recomposeSBTensor bv bw cs' of
               (tvw, cs'') -> (Tensor (tuw, tvw), cs'')
  recomposeLinMap (TupleBasis bu bv) ws = case recomposeLinMap bu ws of
           (lmu, ws') -> first (lmu⊕) $ recomposeLinMap bv ws'
  recomposeContraLinMap fw dds
         = recomposeContraLinMap fw (fst<$>dds)
          ⊕ recomposeContraLinMap fw (snd<$>dds)
  recomposeContraLinMapTensor fw dds = case ( scalarSpaceWitness :: ScalarSpaceWitness u
                                            , dualSpaceWitness :: DualSpaceWitness u
                                            , dualSpaceWitness :: DualSpaceWitness v ) of
    (ScalarSpaceWitness,DualSpaceWitness,DualSpaceWitness) -> uncurryLinearMap
         $ LinearMap ( fromLinearMap . curryLinearMap
                         $ recomposeContraLinMapTensor fw
                                 (fmap (\(LinearMap(Tensor tu,_))->LinearMap tu) dds)
                     , fromLinearMap . curryLinearMap
                         $ recomposeContraLinMapTensor fw
                                 (fmap (\(LinearMap(_,Tensor tv))->LinearMap tv) dds) )
  uncanonicallyFromDual = case ( dualSpaceWitness :: DualSpaceWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
        (DualSpaceWitness,DualSpaceWitness)
            -> uncanonicallyFromDual *** uncanonicallyFromDual
  uncanonicallyToDual = case ( dualSpaceWitness :: DualSpaceWitness u
                             , dualSpaceWitness :: DualSpaceWitness v ) of
        (DualSpaceWitness,DualSpaceWitness)
            -> uncanonicallyToDual *** uncanonicallyToDual
  tensorEquality (Tensor (s₀,s₁)) (Tensor (t₀,t₁)) 
      = tensorEquality s₀ t₀ && tensorEquality s₁ t₁
  dualFinitenessWitness = case ( dualFinitenessWitness @u
                               , dualFinitenessWitness @v ) of
      (DualFinitenessWitness DualSpaceWitness
       , DualFinitenessWitness DualSpaceWitness)
          -> DualFinitenessWitness DualSpaceWitness

  
deriving instance (Show (SubBasis u), Show (SubBasis v))
                    => Show (SubBasis (u,v))


instance ∀ s u v .
         ( FiniteDimensional u, FiniteDimensional v
         , Scalar u~s, Scalar v~s, Scalar (DualVector u)~s, Scalar (DualVector v)~s
         , Fractional' (Scalar v) )
            => FiniteDimensional (Tensor s u v) where
  data SubBasis (Tensor s u v) = TensorBasis !(SubBasis u) !(SubBasis v)
  entireBasis = TensorBasis entireBasis entireBasis
  enumerateSubBasis (TensorBasis bu bv)
       = [ u⊗v | u <- enumerateSubBasis bu, v <- enumerateSubBasis bv ]
  subbasisDimension (TensorBasis bu bv) = subbasisDimension bu * subbasisDimension bv
  decomposeLinMap = dlm dualSpaceWitness
   where dlm :: ∀ w . (LSpace w, Scalar w ~ Scalar v) 
                   => DualSpaceWitness w -> ((u⊗v)+>w) -> (SubBasis (u⊗v), DList w)
         dlm DualSpaceWitness muvw = case decomposeLinMap $ curryLinearMap $ muvw of
           (bu, mvwsg) -> first (TensorBasis bu) . go $ mvwsg []
          where (go, _) = tensorLinmapDecompositionhelpers
  decomposeLinMapWithin = dlm dualSpaceWitness
   where dlm :: ∀ w . (LSpace w, Scalar w ~ Scalar v) 
                   => DualSpaceWitness w -> SubBasis (u⊗v)
                          -> ((u⊗v)+>w) -> Either (SubBasis (u⊗v), DList w) (DList w)
         dlm DualSpaceWitness (TensorBasis bu bv) muvw
               = case decomposeLinMapWithin bu $ curryLinearMap $ muvw of
           Left (bu', mvwsg) -> let (_, (bv', ws)) = goWith bv id (mvwsg []) id
                                in Left (TensorBasis bu' bv', ws)
           Right mvwsg -> let (changed, (bv', ws)) = goWith bv id (mvwsg []) id
                          in if changed
                              then Left (TensorBasis bu bv', ws)
                              else Right ws
          where (_, goWith) = tensorLinmapDecompositionhelpers
  recomposeSB (TensorBasis bu bv) = recomposeSBTensor bu bv
  recomposeSBTensor = rst dualSpaceWitness
   where rst :: ∀ w . (FiniteDimensional w, Scalar w ~ s)
                  => DualSpaceWitness w -> SubBasis (u⊗v)
                               -> SubBasis w -> [s] -> ((u⊗v)⊗w, [s])
         rst DualSpaceWitness (TensorBasis bu bv) bw
          = first (arr lassocTensor) . recomposeSBTensor bu (TensorBasis bv bw)
  recomposeLinMap = rlm dualSpaceWitness
   where rlm :: ∀ w . (LSpace w, Scalar w ~ Scalar v) 
                   => DualSpaceWitness w -> SubBasis (u⊗v) -> [w]
                                -> ((u⊗v)+>w, [w])
         rlm DualSpaceWitness (TensorBasis bu bv) ws
             = ( uncurryLinearMap $ fst . recomposeLinMap bu
                           $ unfoldr (pure . recomposeLinMap bv) ws
               , drop (subbasisDimension bu * subbasisDimension bv) ws )
  recomposeContraLinMap = case dualSpaceWitness :: DualSpaceWitness u of
     DualSpaceWitness -> recomposeContraLinMapTensor
  recomposeContraLinMapTensor = rclt dualSpaceWitness dualSpaceWitness
   where rclt :: ∀ u' w f . ( FiniteDimensional u', Scalar u' ~ s
                            , LinearSpace w, Scalar w ~ s
                            , Hask.Functor f )
                  => DualSpaceWitness u -> DualSpaceWitness u'
                   -> (f (Scalar w) -> w)
                    -> f (Tensor s u v +> DualVector u')
                    -> (Tensor s u v ⊗ u') +> w
         rclt DualSpaceWitness DualSpaceWitness fw dds
              = uncurryLinearMap . uncurryLinearMap
                             . fmap (curryLinearMap) . curryLinearMap
               $ recomposeContraLinMapTensor fw $ fmap (arr curryLinearMap) dds
  uncanonicallyToDual = case ( dualSpaceWitness :: DualSpaceWitness u
                             , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> fmap uncanonicallyToDual 
            >>> transposeTensor >>> fmap uncanonicallyToDual
            >>> transposeTensor >>> arr fromTensor
  uncanonicallyFromDual = case ( dualSpaceWitness :: DualSpaceWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualSpaceWitness, DualSpaceWitness) -> arr asTensor
            >>> fmap uncanonicallyFromDual 
            >>> transposeTensor >>> fmap uncanonicallyFromDual
            >>> transposeTensor
  tensorEquality = tensTensorEquality
  dualFinitenessWitness = case ( dualFinitenessWitness @u
                               , dualFinitenessWitness @v ) of
      (DualFinitenessWitness DualSpaceWitness
       , DualFinitenessWitness DualSpaceWitness)
          -> DualFinitenessWitness DualSpaceWitness
 
tensTensorEquality :: ∀ s u v w . ( FiniteDimensional u, FiniteDimensional v, TensorSpace w
                                  , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
                                  , Eq w )
       => Tensor s (Tensor s u v) w -> Tensor s (Tensor s u v) w -> Bool
tensTensorEquality (Tensor s) (Tensor t)
    = tensorEquality (Tensor s :: Tensor s u (v⊗w)) (Tensor t)


tensorLinmapDecompositionhelpers
      :: ( FiniteDimensional v, LSpace w , Scalar v~s, Scalar w~s )
      => ( [v+>w] -> (SubBasis v, DList w)
         , SubBasis v -> DList w -> [v+>w] -> DList (v+>w)
                        -> (Bool, (SubBasis v, DList w)) )
tensorLinmapDecompositionhelpers = (go, goWith)
   where go [] = decomposeLinMap zeroV
         go (mvw:mvws) = case decomposeLinMap mvw of
              (bv, cfs) -> snd (goWith bv cfs mvws (mvw:))
         goWith bv prevdc [] prevs = (False, (bv, prevdc))
         goWith bv prevdc (mvw:mvws) prevs = case decomposeLinMapWithin bv mvw of
              Right cfs -> goWith bv (prevdc . cfs) mvws (prevs . (mvw:))
              Left (bv', cfs) -> first (const True)
                                 ( goWith bv' (regoWith bv' (prevs[]) . cfs)
                                     mvws (prevs . (mvw:)) )
         regoWith _ [] = id
         regoWith bv (mvw:mvws) = case decomposeLinMapWithin bv mvw of
              Right cfs -> cfs . regoWith bv mvws
              Left _ -> error $
               "Misbehaved FiniteDimensional instance: `decomposeLinMapWithin` should,\
             \\nif it cannot decompose in the given basis, do so in a proper\
             \\nsuperbasis of the given one (so that any vector that could be\
             \\ndecomposed in the old basis can also be decomposed in the new one)."
  
deriving instance (Show (SubBasis u), Show (SubBasis v))
             => Show (SubBasis (Tensor s u v))

instance ∀ s v . (FiniteDimensional v, Scalar v ~ s)
        => Eq (SymmetricTensor s v) where
  SymTensor t == SymTensor u = t==u

instance ∀ s v .
         ( FiniteDimensional v, Scalar v~s, Scalar (DualVector v)~s
         , RealFloat' s )
            => FiniteDimensional (SymmetricTensor s v) where
  newtype SubBasis (SymmetricTensor s v) = SymTensBasis (SubBasis v)
  entireBasis = SymTensBasis entireBasis
  enumerateSubBasis (SymTensBasis b) = do
        v:vs <- tails $ enumerateSubBasis b
        squareV v
          : [ (squareV (v^+^w) ^-^ squareV v ^-^ squareV w) ^* sqrt¹₂ | w <- vs ]
   where sqrt¹₂ = sqrt 0.5
  subbasisDimension (SymTensBasis b) = (n*(n+1))`quot`2
                           -- dim Sym(𝑘,𝑉) = nCr (dim 𝑉 + 𝑘 - 1, 𝑘)
                           -- dim Sym(2,𝑉) = nCr (𝑛 + 1, 2) = 𝑛⋅(𝑛+1)/2
   where n = subbasisDimension b
  decomposeLinMap = dclm dualFinitenessWitness
   where dclm (DualFinitenessWitness DualSpaceWitness :: DualFinitenessWitness v)
                (LinearMap f)
                    = (SymTensBasis bf, rmRedundant 0 . symmetrise $ dlw [])
          where rmRedundant _ [] = id
                rmRedundant k (row:rest)
                    = (sclOffdiag (drop k row)++) . rmRedundant (k+1) rest
                symmetrise l = zipWith (zipWith (^+^)) lm $ transpose lm
                 where lm = matr l
                matr [] = []
                matr l = case splitAt n l of
                    (row,rest) -> row : matr rest
                n = case subbasisDimension bf of
                      nbf | nbf == subbasisDimension bf'  -> nbf
                (LinMapBasis bf bf', dlw)
                    = decomposeLinMap $ asLinearMap . lassocTensor $ f
                sclOffdiag (d:o) = 0.5*^d : ((^*sqrt¹₂)<$>o)
         sqrt¹₂ = sqrt 0.5 :: s
  recomposeSB = rclm dualSpaceWitness
   where rclm (DualSpaceWitness :: DualSpaceWitness v) (SymTensBasis b) ws
           = case recomposeSB (TensorBasis b b)
                    $ mkSym (subbasisDimension b) (repeat id) ws of
              (t, remws) -> (SymTensor t, remws)
         mkSym _ _ [] = []
         mkSym 0 _ ws = ws
         mkSym n (sd₀:sds) ws = let (d:o,rest) = splitAt n ws
                                    oscld = (sqrt 0.5*)<$>o
                                in sd₀ [] ++ [d] ++ oscld
                                     ++ mkSym (n-1) (zipWith (.) sds $ (:)<$>oscld) rest
  recomposeLinMap = rclm dualFinitenessWitness
   where rclm (DualFinitenessWitness DualSpaceWitness :: DualFinitenessWitness v)
                  (SymTensBasis b) ws
           = case recomposeLinMap (LinMapBasis b b)
                    $ mkSym (subbasisDimension b) (repeat id) ws of
              (f, remws) -> (LinearMap $ rassocTensor . asTensor $ f, remws)
         mkSym _ _ [] = []
         mkSym 0 _ ws = ws
         mkSym n (sd₀:sds) ws = let (d:o,rest) = splitAt n ws
                                    oscld = (sqrt 0.5*^)<$>o
                                in sd₀ [] ++ [d] ++ oscld
                                     ++ mkSym (n-1) (zipWith (.) sds $ (:)<$>oscld) rest
  recomposeSBTensor = rcst
   where rcst :: ∀ w . (FiniteDimensional w, Scalar w ~ s)
                => SubBasis (SymmetricTensor s v) -> SubBasis w
                   -> [s] -> (Tensor s (SymmetricTensor s v) w, [s])
         rcst (SymTensBasis b) bw μs
           = case recomposeSBTensor (TensorBasis b b) bw
                    $ mkSym (subbasisDimension bw) (subbasisDimension b) (repeat id) μs of
              (Tensor t, remws) -> ( Tensor $ Tensor t
                                      :: Tensor s (SymmetricTensor s v) w
                                   , remws )
         mkSym _ _ _ [] = []
         mkSym _ 0 _ ws = ws
         mkSym nw n (sd₀:sds) ws = let (d:o,rest) = multiSplit nw n ws
                                       oscld = map (sqrt 0.5*)<$>o
                                   in concat (sd₀ []) ++ d ++ concat oscld
                                       ++ mkSym nw (n-1) (zipWith (.) sds $ (:)<$>oscld) rest
  recomposeContraLinMap f tenss = case dualSpaceWitness @v of
     DualSpaceWitness ->
             LinearMap . arr (rassocTensor . asTensor) . rcCLM dualFinitenessWitness f
                                    $ fmap getSymmetricTensor tenss
   where rcCLM :: (Hask.Functor f, LinearSpace w, s~Scalar w)
           => DualFinitenessWitness v
                 -> (f s->w) -> f (Tensor s (DualVector v) (DualVector v))
                     -> LinearMap s (LinearMap s (DualVector v) v) w
         rcCLM (DualFinitenessWitness DualSpaceWitness) f
            = recomposeContraLinMap f
  uncanonicallyFromDual = case dualFinitenessWitness :: DualFinitenessWitness v of
     DualFinitenessWitness DualSpaceWitness -> LinearFunction
          $ \(SymTensor t) -> SymTensor $ arr fromLinearMap . uncanonicallyFromDual $ t
  uncanonicallyToDual = case dualFinitenessWitness :: DualFinitenessWitness v of
     DualFinitenessWitness DualSpaceWitness -> LinearFunction
          $ \(SymTensor t) -> SymTensor $ uncanonicallyToDual . arr asLinearMap $ t
  dualFinitenessWitness = case dualFinitenessWitness @v of
      DualFinitenessWitness DualSpaceWitness
          -> DualFinitenessWitness DualSpaceWitness
  
deriving instance (Show (SubBasis v)) => Show (SubBasis (SymmetricTensor s v))


instance ∀ s u v .
         ( LSpace u, FiniteDimensional u, FiniteDimensional v
         , Scalar u~s, Scalar v~s, Scalar (DualVector v)~s, Fractional' (Scalar v) )
            => FiniteDimensional (LinearMap s u v) where
  data SubBasis (LinearMap s u v) = LinMapBasis !(SubBasis (DualVector u)) !(SubBasis v)
  entireBasis = case ( dualFinitenessWitness :: DualFinitenessWitness u
                     , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness)
           -> case entireBasis of TensorBasis bu bv -> LinMapBasis bu bv
  enumerateSubBasis
          = case ( dualFinitenessWitness :: DualFinitenessWitness u
                 , dualSpaceWitness :: DualSpaceWitness v )  of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness) -> \(LinMapBasis bu bv)
                   -> arr (fmap $ getVSCCoercion asLinearMap) . enumerateSubBasis $ TensorBasis bu bv
  subbasisDimension (LinMapBasis bu bv) 
          = case ( dualFinitenessWitness :: DualFinitenessWitness u ) of
     (DualFinitenessWitness _) -> subbasisDimension bu * subbasisDimension bv
  decomposeLinMap = case ( dualFinitenessWitness :: DualFinitenessWitness u
                         , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness)
              -> first (\(TensorBasis bu bv)->LinMapBasis bu bv)
                    . decomposeLinMap . coerce
  decomposeLinMapWithin = case ( dualFinitenessWitness :: DualFinitenessWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness)
        -> \(LinMapBasis bu bv) m
         -> case decomposeLinMapWithin (TensorBasis bu bv) (coerce m) of
              Right ws -> Right ws
              Left (TensorBasis bu' bv', ws) -> Left (LinMapBasis bu' bv', ws)
  recomposeSB = case ( dualFinitenessWitness :: DualFinitenessWitness u
                     , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness) -> \(LinMapBasis bu bv)
        -> recomposeSB (TensorBasis bu bv) >>> first (arr fromTensor)
  recomposeSBTensor = case ( dualFinitenessWitness :: DualFinitenessWitness u
                           , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness) -> \(LinMapBasis bu bv) bw
        -> recomposeSBTensor (TensorBasis bu bv) bw >>> first coerce
  recomposeLinMap = rlm dualFinitenessWitness dualSpaceWitness
   where rlm :: ∀ w . (LSpace w, Scalar w ~ Scalar v) 
                   => DualFinitenessWitness u -> DualSpaceWitness w -> SubBasis (u+>v) -> [w]
                                -> ((u+>v)+>w, [w])
         rlm (DualFinitenessWitness DualSpaceWitness) DualSpaceWitness (LinMapBasis bu bv) ws
             = ( coUncurryLinearMap . fromLinearMap $ fst . recomposeLinMap bu
                           $ unfoldr (pure . recomposeLinMap bv) ws
               , drop (subbasisDimension bu * subbasisDimension bv) ws )
  recomposeContraLinMap = case ( dualFinitenessWitness :: DualFinitenessWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness) -> \fw dds
       -> argFromTensor $ recomposeContraLinMapTensor fw $ fmap (arr asLinearMap) dds
  recomposeContraLinMapTensor = rclmt dualFinitenessWitness dualSpaceWitness dualSpaceWitness
   where rclmt :: ∀ f u' w . ( LinearSpace w, FiniteDimensional u'
                             , Scalar w ~ s, Scalar u' ~ s
                             , Hask.Functor f )
                  => DualFinitenessWitness u -> DualSpaceWitness v -> DualSpaceWitness u'
                   -> (f (Scalar w) -> w) -> f ((u+>v)+>DualVector u') -> ((u+>v)⊗u')+>w
         rclmt (DualFinitenessWitness DualSpaceWitness)
                    DualSpaceWitness DualSpaceWitness fw dds
          = uncurryLinearMap . coUncurryLinearMap
           . fmap curryLinearMap . coCurryLinearMap . argFromTensor
             $ recomposeContraLinMapTensor fw
               $ fmap (arr $ asLinearMap . coCurryLinearMap) dds
  uncanonicallyToDual = case ( dualFinitenessWitness :: DualFinitenessWitness u
                             , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness)
           -> arr asTensor >>> fmap uncanonicallyToDual >>> transposeTensor
              >>> fmap uncanonicallyToDual >>> transposeTensor
  uncanonicallyFromDual = case ( dualFinitenessWitness :: DualFinitenessWitness u
                               , dualSpaceWitness :: DualSpaceWitness v ) of
     (DualFinitenessWitness DualSpaceWitness, DualSpaceWitness)
           -> arr fromTensor <<< fmap uncanonicallyFromDual <<< transposeTensor
              <<< fmap uncanonicallyFromDual <<< transposeTensor

  tensorEquality = lmTensorEquality
  dualFinitenessWitness = case ( dualFinitenessWitness @u
                               , dualFinitenessWitness @v ) of
      (DualFinitenessWitness DualSpaceWitness
       , DualFinitenessWitness DualSpaceWitness)
          -> DualFinitenessWitness DualSpaceWitness

lmTensorEquality :: ∀ s u v w . ( FiniteDimensional v, TensorSpace w
                                , FiniteDimensional u
                                , Scalar u ~ s, Scalar v ~ s, Scalar w ~ s
                                , Eq w )
       => Tensor s (LinearMap s u v) w -> Tensor s (LinearMap s u v) w -> Bool
lmTensorEquality (Tensor s) (Tensor t) = case dualFinitenessWitness @u of
      DualFinitenessWitness DualSpaceWitness
         -> tensorEquality (Tensor s :: Tensor s (DualVector u) (v⊗w)) (Tensor t)

deriving instance (Show (SubBasis (DualVector u)), Show (SubBasis v))
             => Show (SubBasis (LinearMap s u v))


infixr 0 \$

-- | Inverse function application, aka solving of a linear system:
--   
-- @
-- f '\$' f '$' v  ≡  v
-- 
-- f '$' f '\$' u  ≡  u
-- @
-- 
-- If @f@ does not have full rank, the behaviour is undefined. However, it
-- does not need to be a proper isomorphism: the
-- first of the above equations is still fulfilled if only @f@ is /injective/
-- (overdetermined system) and the second if it is /surjective/.
-- 
-- If you want to solve for multiple RHS vectors, be sure to partially
-- apply this operator to the linear map, like
-- 
-- @
-- map (f '\$') [v₁, v₂, ...]
-- @
-- 
-- Since most of the work is actually done in triangularising the operator,
-- this may be much faster than
-- 
-- @
-- [f '\$' v₁, f '\$' v₂, ...]
-- @
(\$) :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
          => (u+>v) -> v -> u
(\$) m
  | du > dv    = ((applyLinear-+$>unsafeRightInverse m)-+$>)
  | du < dv    = ((applyLinear-+$>unsafeLeftInverse m)-+$>)
  | otherwise  = let v's = dualBasis $ mdecomp []
                     (mbas, mdecomp) = decomposeLinMap m
                 in fst . \v -> recomposeSB mbas [ maybe 0 (<.>^v) v' | v' <- v's ]
 where du = subbasisDimension (entireBasis :: SubBasis u)
       dv = subbasisDimension (entireBasis :: SubBasis v)
    
{-# DEPRECATED (\$) "The current inversion algorithm is wrong in rare edge cases. It is also dubious how useful it is given that 'SimpleSpace' has in practice just Euclidean-isomorphic spaces as instances, for which off-the-shelf matrix inversion could be used. These functions will probably be removed in favour of something e.g. conjugate-gradient based." #-}

{-# DEPRECATED pseudoInverse "The current inversion algorithm is wrong in rare edge cases. It is also dubious how useful it is given that 'SimpleSpace' has in practice just Euclidean-isomorphic spaces as instances, for which off-the-shelf matrix inversion could be used. These functions will probably be removed in favour of something e.g. conjugate-gradient based." #-}

pseudoInverse :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
          => (u+>v) -> v+>u
pseudoInverse m
  | du > dv    = unsafeRightInverse m
  | du < dv    = unsafeLeftInverse m
  | otherwise  = unsafeInverse m
 where du = subbasisDimension (entireBasis :: SubBasis u)
       dv = subbasisDimension (entireBasis :: SubBasis v)

-- | If @f@ is injective, then
-- 
-- @
-- unsafeLeftInverse f . f  ≡  id
-- @
unsafeLeftInverse :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
                     => (u+>v) -> v+>u
unsafeLeftInverse = uli dualSpaceWitness dualSpaceWitness
 where uli :: DualSpaceWitness u -> DualSpaceWitness v -> (u+>v) -> v+>u
       uli DualSpaceWitness DualSpaceWitness m
             = unsafeInverse (m' . (fmap uncanonicallyToDual $ m))
                         . m' . arr uncanonicallyToDual
        where m' = adjoint $ m :: DualVector v +> DualVector u

-- | If @f@ is surjective, then
-- 
-- @
-- f . unsafeRightInverse f  ≡  id
-- @
unsafeRightInverse :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
                     => (u+>v) -> v+>u
unsafeRightInverse = uri dualSpaceWitness dualSpaceWitness
 where uri :: DualSpaceWitness u -> DualSpaceWitness v -> (u+>v) -> v+>u
       uri DualSpaceWitness DualSpaceWitness m
             = (fmap uncanonicallyToDual $ m')
                          . unsafeInverse (m . (fmap uncanonicallyToDual $ m'))
        where m' = adjoint $ m :: DualVector v +> DualVector u

-- | Invert an isomorphism. For other linear maps, the result is undefined.
unsafeInverse :: ( FiniteDimensional u, SimpleSpace v, Scalar u ~ Scalar v )
          => (u+>v) -> v+>u
unsafeInverse m = recomposeContraLinMap (fst . recomposeSB mbas)
                                        $ [maybe zeroV id v' | v'<-v's]
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m


-- | The <https://en.wikipedia.org/wiki/Riesz_representation_theorem Riesz representation theorem>
--   provides an isomorphism between a Hilbert space and its (continuous) dual space.
riesz :: ∀ v . ( FiniteDimensional v, InnerSpace v
               , SimpleSpace v )
                 => DualVector v -+> v
riesz = case dualFinitenessWitness @v of
  DualFinitenessWitness DualSpaceWitness
      -> arr . unsafeInverse $ arr coRiesz

sRiesz :: ∀ v . FiniteDimensional v => DualSpace v -+> v
sRiesz = case ( scalarSpaceWitness :: ScalarSpaceWitness v
              , dualSpaceWitness :: DualSpaceWitness v ) of
 (ScalarSpaceWitness,DualSpaceWitness) -> LinearFunction $ \dv ->
       let (bas, compos) = decomposeLinMap $ dv
       in fst . recomposeSB bas $ compos []

coRiesz :: ∀ v . (LSpace v, InnerSpace v) => v -+> DualVector v
coRiesz = case ( scalarSpaceWitness :: ScalarSpaceWitness v
               , dualSpaceWitness :: DualSpaceWitness v ) of
 (ScalarSpaceWitness,DualSpaceWitness)
      -> fromFlatTensor . arr asTensor . sampleLinearFunction . inner

-- | Functions are generally a pain to display, but since linear functionals
--   in a Hilbert space can be represented by /vectors/ in that space,
--   this can be used for implementing a 'Show' instance.
showsPrecAsRiesz :: ∀ v . ( FiniteDimensional v, InnerSpace v, Show v
                          , HasBasis (Scalar v), Basis (Scalar v) ~ () )
                      => Int -> DualSpace v -> ShowS
showsPrecAsRiesz = case ( scalarSpaceWitness :: ScalarSpaceWitness v
                        , dualSpaceWitness :: DualSpaceWitness v ) of
 (ScalarSpaceWitness,DualSpaceWitness)
      -> \p dv -> showParen (p>0) $ ("().<"++) . showsPrec 7 (sRiesz$dv)

instance Show (LinearMap ℝ (ZeroDim ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V0 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ ℝ ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V1 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V2 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V3 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V4 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance ∀ s v w .
         ( FiniteDimensional v, InnerSpace v, Show v
         , FiniteDimensional w, InnerSpace w, Show w
         , Scalar v ~ s, Scalar w ~ s
         , HasBasis s, Basis s ~ () )
         => Show (LinearMap s (v,w) s ) where
  showsPrec = case ( dualSpaceWitness :: DualSpaceWitness v
                   , dualSpaceWitness :: DualSpaceWitness w ) of
      (DualSpaceWitness, DualSpaceWitness) -> showsPrecAsRiesz

class TensorDecomposable u => RieszDecomposable u where
  rieszDecomposition :: (FiniteDimensional v, v ~ DualVector v, Scalar v ~ Scalar u)
              => (v +> u) -> [(Basis u, v)]

instance RieszDecomposable ℝ where
  rieszDecomposition (LinearMap r) = [((), fromFlatTensor $ Tensor r)]
instance ( RieszDecomposable x, RieszDecomposable y
         , Scalar x ~ Scalar y, Scalar (DualVector x) ~ Scalar (DualVector y) )
              => RieszDecomposable (x,y) where
  rieszDecomposition m = map (first Left) (rieszDecomposition $ fmap fst -+$> m)
                      ++ map (first Right) (rieszDecomposition $ fmap snd -+$> m)

instance RieszDecomposable (ZeroDim ℝ) where
  rieszDecomposition _ = []
instance RieszDecomposable (V0 ℝ) where
  rieszDecomposition _ = []
instance RieszDecomposable (V1 ℝ) where
  rieszDecomposition m = [(ex, sRiesz $ fmap (LinearFunction (^._x)) $ m)]
#if MIN_VERSION_free_vector_spaces(0,2,0)
   where ex = e @0
#endif
instance RieszDecomposable (V2 ℝ) where
  rieszDecomposition m = [ (ex, sRiesz $ fmap (LinearFunction (^._x)) $ m)
                         , (ey, sRiesz $ fmap (LinearFunction (^._y)) $ m) ]
#if MIN_VERSION_free_vector_spaces(0,2,0)
   where ex = e @0
         ey = e @1
#endif
instance RieszDecomposable (V3 ℝ) where
  rieszDecomposition m = [ (ex, sRiesz $ fmap (LinearFunction (^._x)) $ m)
                         , (ey, sRiesz $ fmap (LinearFunction (^._y)) $ m)
                         , (ez, sRiesz $ fmap (LinearFunction (^._z)) $ m) ]
#if MIN_VERSION_free_vector_spaces(0,2,0)
   where ex = e @0
         ey = e @1
         ez = e @2
#endif
instance RieszDecomposable (V4 ℝ) where
  rieszDecomposition m = [ (ex, sRiesz $ fmap (LinearFunction (^._x)) $ m)
                         , (ey, sRiesz $ fmap (LinearFunction (^._y)) $ m)
                         , (ez, sRiesz $ fmap (LinearFunction (^._z)) $ m)
                         , (ew, sRiesz $ fmap (LinearFunction (^._w)) $ m) ]
#if MIN_VERSION_free_vector_spaces(0,2,0)
   where ex = e @0
         ey = e @1
         ez = e @2
         ew = e @3
#endif

infixl 7 .<

-- | Outer product of a general @v@-vector and a basis element from @w@.
--   Note that this operation is in general pretty inefficient; it is
--   provided mostly to lay out matrix definitions neatly.
(.<) :: ( FiniteDimensional v, Num' (Scalar v)
        , InnerSpace v, LSpace w, HasBasis w, Scalar v ~ Scalar w )
           => Basis w -> v -> v+>w
bw .< v = sampleLinearFunction $ LinearFunction $ \v' -> recompose [(bw, v<.>v')]


-- | This is the preferred method for showing linear maps, resulting in a
--   matrix view involving the '.<' operator.
--   We don't provide a generic `Show` instance; to make linear maps with
--   your own finite-dimensional type @V@ (with scalar @S@) showable,
--   this is the recommended way:
--
--   @
--   instance RieszDecomposable V where
--     rieszDecomposition = ...
--   instance (FiniteDimensional w, w ~ DualVector w, Scalar w ~ S, Show w)
--         => Show (LinearMap S w V) where
--     showsPrec = rieszDecomposeShowsPrec
--   @
-- 
--   Note that the custom type should always be the /codomain/ type, whereas
--   the domain should be kept parametric.
rieszDecomposeShowsPrec :: ∀ u v s . ( RieszDecomposable u
                                     , FiniteDimensional v, v ~ DualVector v, Show v
                                     , Scalar u ~ s, Scalar v ~ s )
                        => Int -> LinearMap s v u -> ShowS
rieszDecomposeShowsPrec p m = case rieszDecomposition m of
            [] -> ("zeroV"++)
            ((b₀,dv₀):dvs) -> showParen (p>6)
                            $ \s -> showsPrecBasis @u 7 b₀
                                                     . (".<"++) . showsPrec 7 dv₀
                                  $ foldr (\(b,dv)
                                        -> (" ^+^ "++) . showsPrecBasis @u 7 b
                                                       . (".<"++) . showsPrec 7 dv) s dvs
                                  
instance Show (LinearMap s v (ZeroDim s)) where
  show _ = "zeroV"
instance Show (LinearMap s v (V0 s)) where
  show _ = "zeroV"
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V1 ℝ)) where
  showsPrec = rieszDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V2 ℝ)) where
  showsPrec = rieszDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V3 ℝ)) where
  showsPrec = rieszDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V4 ℝ)) where
  showsPrec = rieszDecomposeShowsPrec

instance ( FiniteDimensional v, v ~ DualVector v, Show v
         , RieszDecomposable x, RieszDecomposable y
         , Scalar x ~ s, Scalar y ~ s, Scalar v ~ s
         , Scalar (DualVector x) ~ s, Scalar (DualVector y) ~ s )
              => Show (LinearMap s v (x,y)) where
  showsPrec = case
      (dualSpaceWitness::DualSpaceWitness x, dualSpaceWitness::DualSpaceWitness y) of
      (DualSpaceWitness, DualSpaceWitness) -> rieszDecomposeShowsPrec


infixr 7 .⊗

(.⊗) :: ( TensorSpace v, HasBasis v, TensorSpace w
        , Num' (Scalar v), Scalar v ~ Scalar w )
         => Basis v -> w -> v⊗w
b .⊗ w = basisValue b ⊗ w

class (FiniteDimensional v, HasBasis v) => TensorDecomposable v where
  tensorDecomposition :: (TensorSpace w, Scalar w ~ Scalar v)
             => v⊗w -> [(Basis v, w)]
  tensorDecompose' :: (TensorSpace w, Scalar w ~ Scalar v)
             => v⊗w -> Basis v -> w
  showsPrecBasis :: Int -> Basis v -> ShowS

instance ( TensorDecomposable u, TensorSpace v
         , HasBasis u, HasBasis v
         , Num' s, Scalar u ~ s, Scalar v ~ s
         ) => HasBasis (Tensor s u v) where
  type Basis (Tensor s u v) = (Basis u, Basis v)
  basisValue (bu, bv) = basisValue bu ⊗ basisValue bv
  decompose t = [ ((bu,bv),s)
                | (bu,v) <- tensorDecomposition t
                , (bv,s) <- decompose v ]
  decompose' t (bu, bv) = decompose' (tensorDecompose' t bu) bv

instance TensorDecomposable ℝ where
  tensorDecomposition (Tensor r) = [((), r)]
  tensorDecompose' (Tensor r) () = r
  showsPrecBasis _ = shows
instance ∀ x y . ( TensorDecomposable x, TensorDecomposable y
                 , Scalar x ~ Scalar y, Scalar (DualVector x) ~ Scalar (DualVector y) )
              => TensorDecomposable (x,y) where
  tensorDecomposition (Tensor (tx,ty))
                = map (first Left) (tensorDecomposition tx)
               ++ map (first Right) (tensorDecomposition ty)
  tensorDecompose' (Tensor (tx,ty)) (Left bx)
                = tensorDecompose' tx bx
  tensorDecompose' (Tensor (tx,ty)) (Right by)
                = tensorDecompose' ty by
  showsPrecBasis p (Left bx)
      = showParen (p>9) $ ("Left "++) . showsPrecBasis @x 10 bx
  showsPrecBasis p (Right by)
      = showParen (p>9) $ ("Right "++) . showsPrecBasis @y 10 by

instance TensorDecomposable (ZeroDim ℝ) where
  tensorDecomposition _ = []
  tensorDecompose' _ = absurd
  showsPrecBasis _ = absurd
instance TensorDecomposable (V0 ℝ) where
  tensorDecomposition _ = []
  tensorDecompose' _ b = case b of {}
#if MIN_VERSION_free_vector_spaces(0,2,0)
  showsPrecBasis = showsPrec
#else
  showsPrecBasis _ (Mat.E q) = (V0^.q ++)
#endif
instance TensorDecomposable (V1 ℝ) where
#if MIN_VERSION_free_vector_spaces(0,2,0)
  tensorDecomposition (Tensor (V1 w)) = [(e @0, w)]
  tensorDecompose' (Tensor (V1 w)) _ = w
  showsPrecBasis = showsPrec
#else
  tensorDecomposition (Tensor (V1 w)) = [(ex, w)]
  tensorDecompose' (Tensor w) (Mat.E q) = w^.q
  showsPrecBasis _ (Mat.E q) = (V1"ex"^.q ++)
#endif
instance TensorDecomposable (V2 ℝ) where
#if MIN_VERSION_free_vector_spaces(0,2,0)
  tensorDecomposition (Tensor (V2 x y)) = [ (e @0, x), (e @1, y) ]
  tensorDecompose' (Tensor (V2 x y)) b = case getEuclideanBasisIndex b of
    { 0 -> x; 1 -> y }
  showsPrecBasis = showsPrec
#else
  tensorDecomposition (Tensor (V2 x y)) = [ (ex, x), (ey, y) ]
  tensorDecompose' (Tensor w) (Mat.E q) = w^.q
  showsPrecBasis _ (Mat.E q) = (V2"ex""ey"^.q ++)
#endif
instance TensorDecomposable (V3 ℝ) where
#if MIN_VERSION_free_vector_spaces(0,2,0)
  tensorDecomposition (Tensor (V3 x y z)) = [ (e @0, x), (e @1, y), (e @2, z) ]
  tensorDecompose' (Tensor (V3 x y z)) b = case getEuclideanBasisIndex b of
    { 0 -> x; 1 -> y; 2 -> z }
  showsPrecBasis = showsPrec
#else
  tensorDecomposition (Tensor (V3 x y z)) = [ (ex, x), (ey, y), (ez, z) ]
  tensorDecompose' (Tensor w) (Mat.E q) = w^.q
  showsPrecBasis _ (Mat.E q) = (V3"ex""ey""ez"^.q ++)
#endif
instance TensorDecomposable (V4 ℝ) where
#if MIN_VERSION_free_vector_spaces(0,2,0)
  tensorDecomposition (Tensor (V4 x y z w)) = [(e @0,x), (e @1,y), (e @2,z), (e @3,w)]
  tensorDecompose' (Tensor (V4 x y z w)) b = case getEuclideanBasisIndex b of
    { 0 -> x; 1 -> y; 2 -> z; 3 -> w }
  showsPrecBasis = showsPrec
#else
  tensorDecomposition (Tensor (V4 x y z w)) = [ (ex, x), (ey, y), (ez, z), (ew, w) ]
  tensorDecompose' (Tensor w) (Mat.E q) = w^.q
  showsPrecBasis _ (Mat.E q) = (V4"ex""ey""ez""ew"^.q ++)
#endif

instance ∀ u v s
     . ( TensorDecomposable u, TensorDecomposable v
       , Fractional' s, Scalar u ~ s, Scalar v ~ s
       , Scalar (DualVector u) ~ s, Scalar (DualVector v) ~ s )
    => TensorDecomposable (Tensor s u v) where
  tensorDecomposition :: ∀ w . (TensorSpace w, Scalar w ~ s)
      => (Tensor s u v)⊗w -> [((Basis u, Basis v), w)]
  tensorDecomposition (Tensor t) = [ ((bu,bv),w)
                                   | (bu,vw) <- tensorDecomposition @u (Tensor t)
                                   , (bv,w) <- tensorDecomposition @v vw ]
  tensorDecompose' :: ∀ w . (TensorSpace w, Scalar w ~ s)
      => (Tensor s u v)⊗w -> (Basis u, Basis v) -> w
  tensorDecompose' (Tensor t) (bu,bv)
     = tensorDecompose' @v (tensorDecompose' @u (Tensor t) bu) bv
  showsPrecBasis :: Int -> (Basis u, Basis v) -> ShowS
  showsPrecBasis = undefined

tensorDecomposeShowsPrec :: ∀ u v s
  . ( TensorDecomposable u, FiniteDimensional v, Show v, Scalar u ~ s, Scalar v ~ s )
                        => Int -> Tensor s u v -> ShowS
tensorDecomposeShowsPrec p t = case tensorDecomposition t of
            [] -> ("zeroV"++)
            ((b₀,dv₀):dvs) -> showParen (p>6)
                            $ \s -> showsPrecBasis @u 7 b₀
                                                     . (".⊗"++) . showsPrec 7 dv₀
                                  $ foldr (\(b,dv)
                                        -> (" ^+^ "++) . showsPrecBasis @u 7 b
                                                       . (".⊗"++) . showsPrec 7 dv) s dvs

instance Show (Tensor s (V0 s) v) where
  show _ = "zeroV"
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (Tensor ℝ (V1 ℝ) v) where
  showsPrec = tensorDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (Tensor ℝ (V2 ℝ) v) where
  showsPrec = tensorDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (Tensor ℝ (V3 ℝ) v) where
  showsPrec = tensorDecomposeShowsPrec
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (Tensor ℝ (V4 ℝ) v) where
  showsPrec = tensorDecomposeShowsPrec

instance ( FiniteDimensional v, v ~ DualVector v, Show v
         , TensorDecomposable x, TensorDecomposable y
         , Scalar x ~ s, Scalar y ~ s, Scalar v ~ s )
              => Show (Tensor s (x,y) v) where
  showsPrec = case
      (dualSpaceWitness::DualSpaceWitness x, dualSpaceWitness::DualSpaceWitness y) of
      (DualSpaceWitness, DualSpaceWitness) -> tensorDecomposeShowsPrec

instance ( TensorDecomposable u
         , Scalar u ~ s )
              => Show (Tensor s (Tensor s u v) w) where
  showsPrec = case (dualSpaceWitness::DualSpaceWitness u) of
      DualSpaceWitness -> undefined


(^) :: Num a => a -> Int -> a
(^) = (Hask.^)
 

type HilbertSpace v = (LSpace v, InnerSpace v, DualVector v ~ v)

type RealFloat' s = (RealFrac' s, Floating s)

type SimpleSpace v = ( FiniteDimensional v, FiniteDimensional (DualVector v)
                     , SemiInner v, SemiInner (DualVector v)
                     , RealFrac' (Scalar v) )


instance ∀ s u v .
         ( FiniteDimensional u, LSpace v, FiniteFreeSpace v
         , Scalar u~s, Scalar v~s ) => FiniteFreeSpace (LinearMap s u v) where
  freeDimension _ = subbasisDimension (entireBasis :: SubBasis u)
                       * freeDimension ([]::[v])
  toFullUnboxVect = decomposeLinMapWithin entireBasis >>> \case
            Right l -> UArr.concat $ toFullUnboxVect <$> l []
  unsafeFromFullUnboxVect arrv = fst . recomposeLinMap entireBasis
          $ [unsafeFromFullUnboxVect $ UArr.slice (dv*j) dv arrv | j <- [0 .. du-1]]
   where du = subbasisDimension (entireBasis :: SubBasis u)
         dv = freeDimension ([]::[v])

instance ∀ s u v .
         ( LSpace u, FiniteDimensional (DualVector u), LSpace v, FiniteFreeSpace v
         , Scalar u~s, Scalar v~s, Scalar (DualVector u)~s, Scalar (DualVector v)~s )
               => FiniteFreeSpace (Tensor s u v) where
  freeDimension _ = subbasisDimension (entireBasis :: SubBasis (DualVector u))
                        * freeDimension ([]::[v])
  toFullUnboxVect = arr asLinearMap >>> decomposeLinMapWithin entireBasis >>> \case
            Right l -> UArr.concat $ toFullUnboxVect <$> l []
  unsafeFromFullUnboxVect arrv = fromLinearMap $ fst . recomposeLinMap entireBasis
          $ [unsafeFromFullUnboxVect $ UArr.slice (dv*j) dv arrv | j <- [0 .. du-1]]
   where du = subbasisDimension (entireBasis :: SubBasis (DualVector u))
         dv = freeDimension ([]::[v])
  
instance ∀ s u v .
         ( FiniteDimensional u, LSpace v, FiniteFreeSpace v
         , Scalar u~s, Scalar v~s ) => FiniteFreeSpace (LinearFunction s u v) where
  freeDimension _ = subbasisDimension (entireBasis :: SubBasis u)
                       * freeDimension ([]::[v])
  toFullUnboxVect f = toFullUnboxVect (arr f :: LinearMap s u v)
  unsafeFromFullUnboxVect arrv = arr (unsafeFromFullUnboxVect arrv :: LinearMap s u v)
                                     
  

-- | For real matrices, this boils down to 'transpose'.
--   For free complex spaces it also incurs complex conjugation.
--   
-- The signature can also be understood as
--
-- @
-- adjoint :: (v +> w) -> (DualVector w +> DualVector v)
-- @
-- 
-- Or
--
-- @
-- adjoint :: (DualVector v +> DualVector w) -> (w +> v)
-- @
-- 
-- But /not/ @(v+>w) -> (w+>v)@, in general (though in a Hilbert space, this too is
-- equivalent, via 'riesz' isomorphism).
adjoint :: ∀ v w . (LinearSpace v, LinearSpace w, Scalar v ~ Scalar w)
               => (v +> DualVector w) -+> (w +> DualVector v)
adjoint = case ( dualSpaceWitness :: DualSpaceWitness v
               , dualSpaceWitness :: DualSpaceWitness w ) of
   (DualSpaceWitness, DualSpaceWitness)
          -> arr fromTensor . transposeTensor . arr asTensor




multiSplit :: Int -> Int -> [a] -> ([[a]], [a])
multiSplit chunkSize 0 l = ([],l)
multiSplit chunkSize nChunks l = case splitAt chunkSize l of
    (chunk, rest) -> first (chunk:) $ multiSplit chunkSize (nChunks-1) rest
