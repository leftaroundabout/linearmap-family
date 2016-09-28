-- |
-- Module      : Math.VectorSpace.Docile
-- Copyright   : (c) Justus Sagemüller 2016
-- License     : GPL v3
-- 
-- Maintainer  : (@) sagemueller $ geo.uni-koeln.de
-- Stability   : experimental
-- Portability : portable
-- 


{-# LANGUAGE CPP                  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UnicodeSyntax        #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ConstraintKinds      #-}

module Math.VectorSpace.Docile where

import Math.LinearMap.Category.Class
import Math.LinearMap.Category.Instances
import Math.LinearMap.Asserted

import Data.Tree (Tree(..), Forest)
import Data.List (sortBy, foldl')
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Ord (comparing)
import Data.List (maximumBy, unfoldr)
import Data.Foldable (toList)
import Data.Semigroup

import Data.VectorSpace
import Data.Basis

import Prelude ()
import qualified Prelude as Hask

import Control.Category.Constrained.Prelude hiding ((^))
import Control.Arrow.Constrained

import Linear ( V0(V0), V1(V1), V2(V2), V3(V3), V4(V4)
              , _x, _y, _z, _w )
import qualified Data.Vector.Unboxed as UArr
import Data.VectorSpace.Free
import Math.VectorSpace.ZeroDimensional
import qualified Linear.Matrix as Mat
import qualified Linear.Vector as Mat
import Control.Lens ((^.))
import Data.Coerce

import Numeric.IEEE




-- | 'SemiInner' is the class of vector spaces with finite subspaces in which
--   you can define a basis that can be used to project from the whole space
--   into the subspace. The usual application is for using a kind of
--   <https://en.wikipedia.org/wiki/Galerkin_method Galerkin method> to
--   give an approximate solution (see '\$') to a linear equation in a possibly
--   infinite-dimensional space.
-- 
--   Of course, this also works for spaces which are already finite-dimensional themselves.
class LSpace v => SemiInner v where
  -- | Lazily enumerate choices of a basis of functionals that can be made dual
  --   to the given vectors, in order of preference (which roughly means, large in
  --   the normal direction.) I.e., if the vector @𝑣@ is assigned early to the
  --   dual vector @𝑣'@, then @(𝑣' $ 𝑣)@ should be large and all the other products
  --   comparably small.
  -- 
  --   The purpose is that we should be able to make this basis orthonormal
  --   with a ~Gaussian-elimination approach, in a way that stays numerically
  --   stable. This is otherwise known as the /choice of a pivot element/.
  -- 
  --   For simple finite-dimensional array-vectors, you can easily define this
  --   method using 'cartesianDualBasisCandidates'.
  dualBasisCandidates :: [(Int,v)] -> Forest (Int, DualVector v)

cartesianDualBasisCandidates
     :: [DualVector v]  -- ^ Set of canonical basis functionals.
     -> (v -> [ℝ])      -- ^ Decompose a vector in /absolute value/ components.
                        --   the list indices should correspond to those in
                        --   the functional list.
     -> ([(Int,v)] -> Forest (Int, DualVector v))
                        -- ^ Suitable definition of 'dualBasisCandidates'.
cartesianDualBasisCandidates dvs abss vcas = go 0 sorted
 where sorted = sortBy (comparing $ negate . snd . snd)
                       [ (i, (av, maximum av)) | (i,v)<-vcas, let av = abss v ]
       go k ((i,(av,_)):scs)
          | k<n   = Node (i, dv) (go (k+1) [(i',(zeroAt j av',m)) | (i',(av',m))<-scs])
                                : go k scs
        where (j,_) = maximumBy (comparing snd) $ zip jfus av
              dv = dvs !! j
       go _ _ = []
       
       jfus = [0 .. n-1]
       n = length dvs
       
       zeroAt :: Int -> [ℝ] -> [ℝ]
       zeroAt _ [] = []
       zeroAt 0 (_:l) = (-1/0):l
       zeroAt j (e:l) = e : zeroAt (j-1) l

instance (Fractional'' s, SemiInner s) => SemiInner (ZeroDim s) where
  dualBasisCandidates _ = []
instance (Fractional'' s, SemiInner s) => SemiInner (V0 s) where
  dualBasisCandidates _ = []

(<.>^) :: LSpace v => DualVector v -> v -> Scalar v
f<.>^v = (applyDualVector$f)$v

orthonormaliseDuals :: (SemiInner v, LSpace v, RealFrac' (Scalar v))
                          => Scalar v -> [(v, DualVector v)] -> [(v,DualVector v)]
orthonormaliseDuals _ [] = []
orthonormaliseDuals ε ((v,v'₀):ws)
        | ovl > ε    = (v,v') : [(w, w' ^-^ (w'<.>^v)*^v') | (w,w')<-wssys]
        | otherwise  = (v,zeroV) : wssys
 where wssys = orthonormaliseDuals ε ws
       v'₁ = foldl' (\v'i (w,w') -> v'i ^-^ (v'i<.>^w)*^w') (v'₀ ^/ (v'₀<.>^v)) wssys
       v' = v'₁ ^/ ovl
       ovl = v'₁<.>^v

dualBasis :: (SemiInner v, LSpace v, RealFrac' (Scalar v)) => [v] -> [DualVector v]
dualBasis vs = snd <$> orthonormaliseDuals epsilon (zip' vsIxed candidates)
 where zip' ((i,v):vs) ((j,v'):ds)
        | i<j   = zip' vs ((j,v'):ds)
        | i==j  = (v,v') : zip' vs ds
       zip' _ _ = []
       candidates = sortBy (comparing fst) . findBest
                             $ dualBasisCandidates vsIxed
        where findBest [] = []
              findBest (Node iv' bv' : _) = iv' : findBest bv'
       vsIxed = zip [0..] vs

instance SemiInner ℝ where
  dualBasisCandidates = fmap ((`Node`[]) . second recip)
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

instance (Fractional'' s, Ord s, SemiInner s) => SemiInner (V1 s) where
  dualBasisCandidates = fmap ((`Node`[]) . second recip)
                . sortBy (comparing $ negate . abs . snd)
                . filter ((/=0) . snd)

#define FreeSemiInner(V, sabs) \
instance SemiInner (V) where {  \
  dualBasisCandidates            \
     = cartesianDualBasisCandidates Mat.basis (fmap sabs . toList) }
FreeSemiInner(V2 ℝ, abs)
FreeSemiInner(V3 ℝ, abs)
FreeSemiInner(V4 ℝ, abs)

instance ∀ u v . ( SemiInner u, SemiInner v, Scalar u ~ Scalar v ) => SemiInner (u,v) where
  dualBasisCandidates = fmap (\(i,(u,v))->((i,u),(i,v))) >>> unzip
              >>> dualBasisCandidates *** dualBasisCandidates
              >>> combineBaseis False mempty
   where combineBaseis :: Bool -> Set Int
                 -> ( Forest (Int, DualVector u)
                    , Forest (Int, DualVector v) )
                   -> Forest (Int, (DualVector u, DualVector v))
         combineBaseis _ _ ([], []) = []
         combineBaseis False forbidden (Node (i,du) bu' : abu, bv)
            | i`Set.member`forbidden  = combineBaseis False forbidden (abu, bv)
            | otherwise
                 = Node (i, (du, zeroV))
                        (combineBaseis True (Set.insert i forbidden) (bu', bv))
                       : combineBaseis False forbidden (abu, bv)
         combineBaseis True forbidden (bu, Node (i,dv) bv' : abv)
            | i`Set.member`forbidden  = combineBaseis True forbidden (bu, abv)
            | otherwise
                 = Node (i, (zeroV, dv))
                        (combineBaseis False (Set.insert i forbidden) (bu, bv'))
                       : combineBaseis True forbidden (bu, abv)
         combineBaseis _ forbidden (bu, []) = combineBaseis False forbidden (bu,[])
         combineBaseis _ forbidden ([], bv) = combineBaseis True forbidden ([],bv)


instance ∀ s u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ s, Scalar v ~ s )
           => SemiInner (Tensor s u v) where
  dualBasisCandidates = map (fmap (second $ arr transposeTensor . arr asTensor))
                      . dualBasisCandidates
                      . map (second $ arr asLinearMap)

instance ∀ s u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ s, Scalar v ~ s )
           => SemiInner (LinearMap s u v) where
  dualBasisCandidates = sequenceForest
                      . map (second pseudoInverse) -- this is not efficient
   where sequenceForest [] = []
         sequenceForest (x:xs) = [Node x $ sequenceForest xs]
  
(^/^) :: (InnerSpace v, Eq (Scalar v), Fractional (Scalar v)) => v -> v -> Scalar v
v^/^w = case (v<.>w) of
   0 -> 0
   vw -> vw / (w<.>w)

type DList x = [x]->[x]

class (LSpace v, LSpace (Scalar v)) => FiniteDimensional v where
  -- | Whereas 'Basis'-values refer to a single basis vector, a single
  --   'SubBasis' value represents a collection of such basis vectors,
  --   which can be used to associate a vector with a list of coefficients.
  -- 
  --   For spaces with a canonical finite basis, 'SubBasis' does not actually
  --   need to contain any information, it can simply have the full finite
  --   basis as its only value. Even for large sparse spaces, it should only
  --   have a very coarse structure that can be shared by many vectors.
  data SubBasis v :: *
  
  entireBasis :: SubBasis v
  
  enumerateSubBasis :: SubBasis v -> [v]
  
  subbasisDimension :: SubBasis v -> Int
  subbasisDimension = length . enumerateSubBasis
  
  -- | Split up a linear map in “column vectors” WRT some suitable basis.
  decomposeLinMap :: (LSpace w, Scalar w ~ Scalar v) => (v+>w) -> (SubBasis v, DList w)
  
  -- | Expand in the given basis, if possible. Else yield a superbasis of the given
  --   one, in which this /is/ possible, and the decomposition therein.
  decomposeLinMapWithin :: (LSpace w, Scalar w ~ Scalar v)
      => SubBasis v -> (v+>w) -> Either (SubBasis v, DList w) (DList w)
  
  -- | Assemble a vector from coefficients in some basis. Return any excess coefficients.
  recomposeSB :: SubBasis v -> [Scalar v] -> (v, [Scalar v])
  
  recomposeSBTensor :: (FiniteDimensional w, Scalar w ~ Scalar v)
               => SubBasis v -> SubBasis w -> [Scalar v] -> (v⊗w, [Scalar v])
  
  recomposeLinMap :: (LSpace w, Scalar w~Scalar v) => SubBasis v -> [w] -> (v+>w, [w])
  
  -- | Given a function that interprets a coefficient-container as a vector representation,
  --   build a linear function mapping to that space.
  recomposeContraLinMap :: (LinearSpace w, Scalar w ~ Scalar v, Hask.Functor f)
           => (f (Scalar w) -> w) -> f (DualVector v) -> v+>w
  
  recomposeContraLinMapTensor
        :: ( FiniteDimensional u, LinearSpace w
           , Scalar u ~ Scalar v, Scalar w ~ Scalar v, Hask.Functor f )
           => (f (Scalar w) -> w) -> f (DualVector v⊗DualVector u) -> (v⊗u)+>w
  
  -- | The existance of a finite basis gives us an isomorphism between a space
  --   and its dual space. Note that this isomorphism is not natural (i.e. it
  --   depends on the actual choice of basis, unlike everything else in this
  --   library).
  uncanonicallyFromDual :: DualVector v -+> v
  uncanonicallyToDual :: v -+> DualVector v


instance (Num''' s) => FiniteDimensional (ZeroDim s) where
  data SubBasis (ZeroDim s) = ZeroBasis
  entireBasis = ZeroBasis
  enumerateSubBasis ZeroBasis = []
  subbasisDimension ZeroBasis = 0
  recomposeSB ZeroBasis l = (Origin, l)
  recomposeSBTensor ZeroBasis _ l = (Tensor Origin, l)
  recomposeLinMap ZeroBasis l = (LinearMap Origin, l)
  decomposeLinMap _ = (ZeroBasis, id)
  decomposeLinMapWithin ZeroBasis _ = pure id
  recomposeContraLinMap _ _ = LinearMap Origin
  recomposeContraLinMapTensor _ _ = LinearMap Origin
  uncanonicallyFromDual = id
  uncanonicallyToDual = id
  
instance (Num''' s, LinearSpace s) => FiniteDimensional (V0 s) where
  data SubBasis (V0 s) = V0Basis
  entireBasis = V0Basis
  enumerateSubBasis V0Basis = []
  subbasisDimension V0Basis = 0
  recomposeSB V0Basis l = (V0, l)
  recomposeSBTensor V0Basis _ l = (Tensor V0, l)
  recomposeLinMap V0Basis l = (LinearMap V0, l)
  decomposeLinMap _ = (V0Basis, id)
  decomposeLinMapWithin V0Basis _ = pure id
  recomposeContraLinMap _ _ = LinearMap V0
  recomposeContraLinMapTensor _ _ = LinearMap V0
  uncanonicallyFromDual = id
  uncanonicallyToDual = id
  
instance FiniteDimensional ℝ where
  data SubBasis ℝ = RealsBasis
  entireBasis = RealsBasis
  enumerateSubBasis RealsBasis = [1]
  subbasisDimension RealsBasis = 1
  recomposeSB RealsBasis [] = (0, [])
  recomposeSB RealsBasis (μ:cs) = (μ, cs)
  recomposeSBTensor RealsBasis bw = first Tensor . recomposeSB bw
  recomposeLinMap RealsBasis (w:ws) = (LinearMap w, ws)
  decomposeLinMap (LinearMap v) = (RealsBasis, (v:))
  decomposeLinMapWithin RealsBasis (LinearMap v) = pure (v:)
  recomposeContraLinMap fw = LinearMap . fw
  recomposeContraLinMapTensor fw = arr uncurryLinearMap . LinearMap
              . recomposeContraLinMap fw . fmap getTensorProduct
  uncanonicallyFromDual = id
  uncanonicallyToDual = id

#define FreeFiniteDimensional(V, VB, dimens, take, give)        \
instance (Num''' s, LSpace s)                            \
            => FiniteDimensional (V s) where {            \
  data SubBasis (V s) = VB deriving (Show);                             \
  entireBasis = VB;                                      \
  enumerateSubBasis VB = toList $ Mat.identity;      \
  subbasisDimension VB = dimens;                       \
  uncanonicallyFromDual = id;                               \
  uncanonicallyToDual = id;                                  \
  recomposeSB _ (take:cs) = (give, cs);                   \
  recomposeSB b cs = recomposeSB b $ cs ++ [0];        \
  recomposeSBTensor VB bw cs = case recomposeMultiple bw dimens cs of \
                   {(take:[], cs') -> (Tensor (give), cs')};              \
  recomposeLinMap VB (take:ws') = (LinearMap (give), ws');   \
  decomposeLinMap (LinearMap m) = (VB, (toList m ++));          \
  decomposeLinMapWithin VB (LinearMap m) = pure (toList m ++);          \
  recomposeContraLinMap fw mv \
         = LinearMap $ (\v -> fw $ fmap (<.>^v) mv) <$> Mat.identity; \
  recomposeContraLinMapTensor fw mv = LinearMap $ \
       (\v -> fromLinearMap $ recomposeContraLinMap fw \
                $ fmap (\(Tensor q) -> foldl' (^+^) zeroV $ liftA2 (*^) v q) mv) \
                       <$> Mat.identity }
FreeFiniteDimensional(V1, V1Basis, 1, c₀         , V1 c₀         )
FreeFiniteDimensional(V2, V2Basis, 2, c₀:c₁      , V2 c₀ c₁      )
FreeFiniteDimensional(V3, V3Basis, 3, c₀:c₁:c₂   , V3 c₀ c₁ c₂   )
FreeFiniteDimensional(V4, V4Basis, 4, c₀:c₁:c₂:c₃, V4 c₀ c₁ c₂ c₃)

recomposeMultiple :: FiniteDimensional w
              => SubBasis w -> Int -> [Scalar w] -> ([w], [Scalar w])
recomposeMultiple bw n dc
 | n<1        = ([], dc)
 | otherwise  = case recomposeSB bw dc of
           (w, dc') -> first (w:) $ recomposeMultiple bw (n-1) dc'
                                  
deriving instance Show (SubBasis ℝ)
  
instance ( FiniteDimensional u, FiniteDimensional v
         , Scalar u ~ Scalar v )
            => FiniteDimensional (u,v) where
  data SubBasis (u,v) = TupleBasis !(SubBasis u) !(SubBasis v)
  entireBasis = TupleBasis entireBasis entireBasis
  enumerateSubBasis (TupleBasis bu bv)
       = ((,zeroV)<$>enumerateSubBasis bu) ++ ((zeroV,)<$>enumerateSubBasis bv)
  subbasisDimension (TupleBasis bu bv) = subbasisDimension bu + subbasisDimension bv
  decomposeLinMap (LinearMap (fu, fv))
       = case (decomposeLinMap (asLinearMap$fu), decomposeLinMap (asLinearMap$fv)) of
         ((bu, du), (bv, dv)) -> (TupleBasis bu bv, du . dv)
  decomposeLinMapWithin (TupleBasis bu bv) (LinearMap (fu, fv))
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
  recomposeContraLinMapTensor fw dds
     = uncurryLinearMap
         $ LinearMap ( fromLinearMap . curryLinearMap
                         $ recomposeContraLinMapTensor fw (fmap (\(Tensor(tu,_))->tu) dds)
                     , fromLinearMap . curryLinearMap
                         $ recomposeContraLinMapTensor fw (fmap (\(Tensor(_,tv))->tv) dds) )
  uncanonicallyFromDual = uncanonicallyFromDual *** uncanonicallyFromDual
  uncanonicallyToDual = uncanonicallyToDual *** uncanonicallyToDual
  
deriving instance (Show (SubBasis u), Show (SubBasis v))
                    => Show (SubBasis (u,v))


instance ∀ s u v .
         ( FiniteDimensional u, FiniteDimensional v
         , Scalar u~s, Scalar v~s, Fractional' (Scalar v) )
            => FiniteDimensional (Tensor s u v) where
  data SubBasis (Tensor s u v) = TensorBasis !(SubBasis u) !(SubBasis v)
  entireBasis = TensorBasis entireBasis entireBasis
  enumerateSubBasis (TensorBasis bu bv)
       = [ u⊗v | u <- enumerateSubBasis bu, v <- enumerateSubBasis bv ]
  subbasisDimension (TensorBasis bu bv) = subbasisDimension bu * subbasisDimension bv
  decomposeLinMap muvw = case decomposeLinMap $ curryLinearMap $ muvw of
         (bu, mvwsg) -> first (TensorBasis bu) . go id $ mvwsg []
   where (go, _) = tensorLinmapDecompositionhelpers
  decomposeLinMapWithin (TensorBasis bu bv) muvw
               = case decomposeLinMapWithin bu $ curryLinearMap $ muvw of
          Left (bu', mvwsg) -> let (_, (bv', ws)) = goWith bv id (mvwsg []) id
                               in Left (TensorBasis bu' bv', ws)
   where (_, goWith) = tensorLinmapDecompositionhelpers
  recomposeSB (TensorBasis bu bv) = recomposeSBTensor bu bv
  recomposeSBTensor (TensorBasis bu bv) bw
          = first (arr lassocTensor) . recomposeSBTensor bu (TensorBasis bv bw)
  recomposeLinMap (TensorBasis bu bv) ws =
      ( uncurryLinearMap $ fst . recomposeLinMap bu $ unfoldr (pure . recomposeLinMap bv) ws
      , drop (subbasisDimension bu * subbasisDimension bv) ws )
  recomposeContraLinMap = recomposeContraLinMapTensor
  recomposeContraLinMapTensor fw dds
     = uncurryLinearMap . uncurryLinearMap . fmap (curryLinearMap) . curryLinearMap
               $ recomposeContraLinMapTensor fw $ fmap (arr rassocTensor) dds
  uncanonicallyToDual = fmap uncanonicallyToDual 
            >>> transposeTensor >>> fmap uncanonicallyToDual
            >>> transposeTensor
  uncanonicallyFromDual = fmap uncanonicallyFromDual 
            >>> transposeTensor >>> fmap uncanonicallyFromDual
            >>> transposeTensor

tensorLinmapDecompositionhelpers
      :: ( FiniteDimensional v, LSpace w , Scalar v~s, Scalar w~s )
      => ( DList w -> [v+>w] -> (SubBasis v, DList w)
         , SubBasis v -> DList w -> [v+>w] -> DList (v+>w)
                        -> (Bool, (SubBasis v, DList w)) )
tensorLinmapDecompositionhelpers = (go, goWith)
   where go _ [] = decomposeLinMap zeroV
         go prevdc (mvw:mvws) = case decomposeLinMap mvw of
              (bv, cfs) -> snd (goWith bv prevdc mvws (mvw:))
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


instance ∀ s u v .
         ( LSpace u, FiniteDimensional (DualVector u), FiniteDimensional v
         , Scalar u~s, Scalar v~s, Fractional' (Scalar v) )
            => FiniteDimensional (LinearMap s u v) where
  data SubBasis (LinearMap s u v) = LinMapBasis !(SubBasis (DualVector u)) !(SubBasis v)
  entireBasis = case entireBasis of TensorBasis bu bv -> LinMapBasis bu bv
  enumerateSubBasis (LinMapBasis bu bv)
          = arr (fmap asLinearMap) . enumerateSubBasis $ TensorBasis bu bv
  subbasisDimension (LinMapBasis bu bv) = subbasisDimension bu * subbasisDimension bv
  decomposeLinMap = first (\(TensorBasis bv bu)->LinMapBasis bu bv)
                    . decomposeLinMap . coerce
  decomposeLinMapWithin (LinMapBasis bu bv) m
          = case decomposeLinMapWithin (TensorBasis bv bu) (coerce m) of
              Right ws -> Right ws
              Left (TensorBasis bv' bu', ws) -> Left (LinMapBasis bu' bv', ws)
  recomposeSB (LinMapBasis bu bv)
     = recomposeSB (TensorBasis bu bv) >>> first (arr fromTensor)
  recomposeSBTensor (LinMapBasis bu bv) bw
     = recomposeSBTensor (TensorBasis bu bv) bw >>> first coerce
  recomposeLinMap (LinMapBasis bu bv) ws =
      ( coUncurryLinearMap . fmap asTensor $ fst . recomposeLinMap bv
                   $ unfoldr (pure . recomposeLinMap bu) ws
      , drop (subbasisDimension bu * subbasisDimension bv) ws )
  recomposeContraLinMap fw dds = coUncurryLinearMap . fmap fromLinearMap . curryLinearMap
                   $ recomposeContraLinMapTensor fw $ fmap (arr asTensor) dds
  recomposeContraLinMapTensor fw dds
       = uncurryLinearMap . coUncurryLinearMap
         . fmap (fromLinearMap . curryLinearMap) . curryLinearMap
           $ recomposeContraLinMapTensor fw $ fmap (arr $ asTensor . hasteLinearMap) dds
  uncanonicallyToDual = fmap uncanonicallyToDual >>> arr asTensor
             >>> transposeTensor >>> arr fromTensor >>> fmap uncanonicallyToDual
  uncanonicallyFromDual = fmap uncanonicallyFromDual >>> arr asTensor
             >>> transposeTensor >>> arr fromTensor >>> fmap uncanonicallyFromDual
  
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
  | du > dv    = (unsafeRightInverse m $)
  | du < dv    = (unsafeLeftInverse m $)
  | otherwise  = let v's = dualBasis $ mdecomp []
                     (mbas, mdecomp) = decomposeLinMap m
                 in fst . \v -> recomposeSB mbas [v'<.>^v | v' <- v's]
 where du = subbasisDimension (entireBasis :: SubBasis u)
       dv = subbasisDimension (entireBasis :: SubBasis v)
    

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
unsafeLeftInverse m = unsafeInverse (m' . (fmap uncanonicallyToDual $ m))
                         . m' . arr uncanonicallyToDual
 where m' = adjoint $ m :: DualVector v +> DualVector u

-- | If @f@ is surjective, then
-- 
-- @
-- f . unsafeRightInverse f  ≡  id
-- @
unsafeRightInverse :: ∀ u v . ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
                     => (u+>v) -> v+>u
unsafeRightInverse m = (fmap uncanonicallyToDual $ m')
                          . unsafeInverse (m . (fmap uncanonicallyToDual $ m'))
 where m' = adjoint $ m :: DualVector v +> DualVector u

-- | Invert an isomorphism. For other linear maps, the result is undefined.
unsafeInverse :: ( SimpleSpace u, SimpleSpace v, Scalar u ~ Scalar v )
          => (u+>v) -> v+>u
unsafeInverse m = recomposeContraLinMap (fst . recomposeSB mbas) v's
 where v's = dualBasis $ mdecomp []
       (mbas, mdecomp) = decomposeLinMap m


-- | The <https://en.wikipedia.org/wiki/Riesz_representation_theorem Riesz representation theorem>
--   provides an isomorphism between a Hilbert space and its (continuous) dual space.
riesz :: (FiniteDimensional v, InnerSpace v) => DualVector v -+> v
riesz = LinearFunction $ \dv ->
       let (bas, compos) = decomposeLinMap $ sampleLinearFunction $ applyDualVector $ dv
       in fst . recomposeSB bas $ compos []

sRiesz :: FiniteDimensional v => DualSpace v -+> v
sRiesz = LinearFunction $ \dv ->
       let (bas, compos) = decomposeLinMap $ dv
       in fst . recomposeSB bas $ compos []

coRiesz :: (LSpace v, Num''' (Scalar v), InnerSpace v) => v -+> DualVector v
coRiesz = fromFlatTensor . arr asTensor . sampleLinearFunction . inner

-- | Functions are generally a pain to display, but since linear functionals
--   in a Hilbert space can be represented by /vectors/ in that space,
--   this can be used for implementing a 'Show' instance.
showsPrecAsRiesz :: ( FiniteDimensional v, InnerSpace v, Show v
                    , HasBasis (Scalar v), Basis (Scalar v) ~ () )
                      => Int -> DualSpace v -> ShowS
showsPrecAsRiesz p dv = showParen (p>0) $ ("().<"++)
            . showsPrec 7 (sRiesz$dv)

instance Show (LinearMap ℝ (V0 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ ℝ ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V1 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V2 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V3 ℝ) ℝ) where showsPrec = showsPrecAsRiesz
instance Show (LinearMap ℝ (V4 ℝ) ℝ) where showsPrec = showsPrecAsRiesz


infixl 7 .<

-- | Outer product of a general @v@-vector and a basis element from @w@.
--   Note that this operation is in general pretty inefficient; it is
--   provided mostly to lay out matrix definitions neatly.
(.<) :: ( FiniteDimensional v, Num''' (Scalar v)
        , InnerSpace v, LSpace w, HasBasis w, Scalar v ~ Scalar w )
           => Basis w -> v -> v+>w
bw .< v = sampleLinearFunction $ LinearFunction $ \v' -> recompose [(bw, v<.>v')]

instance Show (LinearMap s v (V0 s)) where
  show _ = "zeroV"
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V1 ℝ)) where
  showsPrec p m = showParen (p>6) $ ("ex .< "++)
                       . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._x)) $ m)
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V2 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._x)) $ m)
         . (" ^+^ ey.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._y)) $ m)
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V3 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._x)) $ m)
         . (" ^+^ ey.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._y)) $ m)
         . (" ^+^ ez.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._z)) $ m)
instance (FiniteDimensional v, v ~ DualVector v, Scalar v ~ ℝ, Show v)
              => Show (LinearMap ℝ v (V4 ℝ)) where
  showsPrec p m = showParen (p>6)
              $ ("ex.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._x)) $ m)
         . (" ^+^ ey.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._y)) $ m)
         . (" ^+^ ez.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._z)) $ m)
         . (" ^+^ ew.<"++) . showsPrec 7 (sRiesz $ fmap (LinearFunction (^._w)) $ m)





(^) :: Num a => a -> Int -> a
(^) = (Hask.^)
 

type HilbertSpace v = (LSpace v, InnerSpace v, DualVector v ~ v)

type RealFrac' s = (IEEE s, HilbertSpace s, Scalar s ~ s)
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
         , Scalar u~s, Scalar v~s ) => FiniteFreeSpace (Tensor s u v) where
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
adjoint :: (LSpace v, LSpace w, Scalar v ~ Scalar w)
               => (v +> DualVector w) -+> (w +> DualVector v)
adjoint = arr fromTensor . transposeTensor . arr asTensor
