{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

#ifndef MIN_VERSION_generics_sop
#define MIN_VERSION_generics_sop(x,y,z) 1
#endif

-- | Lenses for "Generics.SOP"
--
-- Orphan instances:
--
-- @
-- 'Wrapped' ('SOP' f xss) -- Also 'Rewrapped'
-- 'Wrapped' ('POP' f xss)
-- 'Field1' ('NP' f (x ': zs)) ('NP' f (y ': zs)) (f x) (f y) -- 'Field2' etc.
-- 'Field1' ('POP' f (x ': zs)) ('NP' f (y ': zs)) (NP f x) (NP f y)
-- @
module Generics.SOP.Lens (
    -- * Representations
    rep, productRep,
    -- * SOP & POP
    sop, pop,
    _SOP, _POP,
    -- * Functors
    _I, _K,
    -- * Products
    npSingleton,
    npHead,
    npTail,
    -- * Sums
    nsSingleton,
    _Z,
    _S,
    -- * DatatypeInfo
    Generics.SOP.Lens.moduleName,
    Generics.SOP.Lens.datatypeName,
    Generics.SOP.Lens.constructorInfo,
    Generics.SOP.Lens.constructorName,
#if MIN_VERSION_generics_sop(0,5,0)
    Generics.SOP.Lens.strictnessInfo,
#endif
    ) where

import Control.Lens
import Generics.SOP hiding (from)
import qualified Generics.SOP as SOP

#if MIN_VERSION_generics_sop(0,5,0)
import Generics.SOP.Metadata
#endif

-------------------------------------------------------------------------------
-- Representations
-------------------------------------------------------------------------------

-- | Convert from the data type to its representation (or back).
--
-- >>> Just 'x' ^. rep
-- SOP (S (Z (I 'x' :* Nil)))
rep :: (Generic a, Generic b) => Iso a b (Rep a) (Rep b)
rep = iso SOP.from SOP.to

-- | Convert from the product data type to its representation (or back)
--
-- >>> ('x', True) ^. productRep
-- I 'x' :* I True :* Nil
--
#if MIN_VERSION_generics_sop(0,3,1)
productRep :: (IsProductType a xs, IsProductType b ys) => Iso a b (NP I xs) (NP I ys)
#else
productRep :: (Generic a, Generic b, Code a ~ '[xs], Code b ~ '[ys]) =>  Iso a b (NP I xs) (NP I ys)
#endif
productRep = rep . sop . nsSingleton

-------------------------------------------------------------------------------
-- SOP & POP
-------------------------------------------------------------------------------

-- | The only field of 'SOP'.
--
-- >>> Just 'x' ^. rep . sop
-- S (Z (I 'x' :* Nil))
sop ::
    forall (f :: k -> *) xss yss.
    Iso (SOP f xss) (SOP f yss) (NS (NP f) xss) (NS (NP f) yss)
sop = iso unSOP SOP

-- | Alias for 'sop'.
_SOP ::
    forall (f :: k -> *) xss yss.
    Iso (SOP f xss) (SOP f yss) (NS (NP f) xss) (NS (NP f) yss)
_SOP = sop

-- | The only field of 'POP'.
pop ::
    forall (f :: k -> *) xss yss.
    Iso (POP f xss) (POP f yss) (NP (NP f) xss) (NP (NP f) yss)
pop = iso unPOP POP

-- | Alias for 'pop'.
_POP ::
    forall (f :: k -> *) xss yss.
    Iso (POP f xss) (POP f yss) (NP (NP f) xss) (NP (NP f) yss)
_POP = pop

instance (t ~ SOP f xss) => Rewrapped (SOP f xss) t
instance Wrapped (SOP f xss) where
    type Unwrapped (SOP f xss) = NS (NP f) xss
    _Wrapped' = sop

instance (t ~ POP f xss) => Rewrapped (POP f xss) t
instance Wrapped (POP f xss) where
    type Unwrapped (POP f xss) = NP (NP f) xss
    _Wrapped' = pop

-------------------------------------------------------------------------------
-- Basic functors
-------------------------------------------------------------------------------

_I :: Iso (I a) (I b) a b
_I = iso unI I

_K :: Iso (K a c) (K b c) a b
_K = iso unK K

instance (t ~ I a) => Rewrapped (I a) t
instance Wrapped (I a) where
    type Unwrapped (I a) = a
    _Wrapped' = _I

instance (t ~ K a b) => Rewrapped (K a b) t
instance Wrapped (K a b) where
    type Unwrapped (K a b) = a
    _Wrapped' = _K

-------------------------------------------------------------------------------
-- Products
-------------------------------------------------------------------------------

npSingleton ::
    forall (f :: k -> *) x y.
    Iso (NP f '[x]) (NP f '[y]) (f x) (f y)
npSingleton = iso g s
  where
    g :: NP f '[x] -> f x
    g (x  :* Nil)   = x
#if __GLASGOW_HASKELL__ < 800
    g _ = error "_NPSingleton"
#endif

    s :: f y -> NP f '[y]
    s y = y :* Nil

type family UnSingleton (xs :: [k]) :: k where
    UnSingleton '[x] = x

instance (t ~ NS f xs, xs ~ '[x]) => Rewrapped (NS f xs) t
instance (xs ~ '[x]) => Wrapped (NS f xs) where
    type Unwrapped (NS f xs) = f (UnSingleton xs)
    _Wrapped' = nsSingleton

npHead ::
    forall (f :: k -> *) x y zs.
    Lens (NP f (x ': zs)) (NP f (y ': zs)) (f x) (f y)
npHead = lens g s
  where
    g :: NP f (x ': zs) -> f x
    g (x  :* _zs)   = x

    s :: NP f (x ': zs) -> f y -> NP f (y ': zs)
    s (_x :*  zs) y = y :* zs

npTail ::
    forall (f :: k -> *) x ys zs.
    Lens (NP f (x ': ys)) (NP f (x ': zs)) (NP f ys) (NP f zs)
npTail = lens g s
  where
    g :: NP f (x ': ys) -> NP f ys
    g (_x :*  ys)    = ys

    s :: NP f (x ': ys) -> NP f zs -> NP f (x ': zs)
    s (x  :* _ys) zs = x :* zs

instance Field1 (NP f (x ': zs)) (NP f (y ': zs)) (f x) (f y) where _1 = npHead
instance Field1 (POP f (x ': zs)) (POP f (y ': zs)) (NP f x) (NP f y) where _1 = _POP . _1

instance Field2 (NP f (a ': x ': zs)) (NP f (a ': y ': zs)) (f x) (f y) where _2 = npTail . _1
instance Field2 (POP f (a ': x ': zs)) (POP f (a ': y ': zs)) (NP f x) (NP f y) where _2 = _POP . _2

instance Field3 (NP f (a ': b ': x ': zs)) (NP f (a ': b ': y ': zs)) (f x) (f y) where _3 = npTail . _2
instance Field3 (POP f (a ': b ': x ': zs)) (POP f (a ': b ': y ': zs)) (NP f x) (NP f y) where _3 = _POP . _3

instance Field4 (NP f (a ': b ': c ': x ': zs)) (NP f (a ': b ': c ': y ': zs)) (f x) (f y) where _4 = npTail . _3
instance Field4 (POP f (a ': b ': c ': x ': zs)) (POP f (a ': b ': c ': y ': zs)) (NP f x) (NP f y) where _4 = _POP . _4

instance Field5 (NP f (a ': b ': c ': d ': x ': zs)) (NP f (a ': b ': c ': d ': y ': zs)) (f x) (f y) where _5 = npTail . _4
instance Field5 (POP f (a ': b ': c ': d ': x ': zs)) (POP f (a ': b ': c ': d ': y ': zs)) (NP f x) (NP f y) where _5 = _POP . _5

instance Field6 (NP f (a ': b ': c ': d ': e ': x ': zs)) (NP f (a ': b ': c ': d ': e ': y ': zs)) (f x) (f y) where _6 = npTail . _5
instance Field6 (POP f (a ': b ': c ': d ': e ': x ': zs)) (POP f (a ': b ': c ': d ': e ': y ': zs)) (NP f x) (NP f y) where _6 = _POP . _6

instance Field7 (NP f' (a ': b ': c ': d ': e ': f ': x ': zs)) (NP f' (a ': b ': c ': d ': e ': f ': y ': zs)) (f' x) (f' y) where _7 = npTail . _6
instance Field7 (POP f' (a ': b ': c ': d ': e ': f ': x ': zs)) (POP f' (a ': b ': c ': d ': e ': f ': y ': zs)) (NP f' x) (NP f' y) where _7 = _POP . _7

instance Field8 (NP f' (a ': b ': c ': d ': e ': f ': g ': x ': zs)) (NP f' (a ': b ': c ': d ': e ': f ': g ': y ': zs)) (f' x) (f' y) where _8 = npTail . _7
instance Field8 (POP f' (a ': b ': c ': d ': e ': f ': g ': x ': zs)) (POP f' (a ': b ': c ': d ': e ': f ': g ': y ': zs)) (NP f' x) (NP f' y) where _8 = _POP . _8

instance Field9 (NP f' (a ': b ': c ': d ': e ': f ': g ': h ': x ': zs)) (NP f' (a ': b ': c ': d ': e ': f ': g ': h ': y ': zs)) (f' x) (f' y) where _9 = npTail . _8
instance Field9 (POP f' (a ': b ': c ': d ': e ': f ': g ': h ': x ': zs)) (POP f' (a ': b ': c ': d ': e ': f ': g ': h ': y ': zs)) (NP f' x) (NP f' y) where _9 = _POP . _9

-------------------------------------------------------------------------------
-- Sums
-------------------------------------------------------------------------------

nsSingleton ::
    forall (f :: k -> *) x y.
    Iso (NS f '[x]) (NS f '[y]) (f x) (f y)
nsSingleton = iso g Z
  where
    g :: NS f '[x] -> f x
    g (Z x)   = x
#if __GLASGOW_HASKELL__ < 800
    g _ = error "singletonS"
#else
    g (S v) = case v of {}
#endif

_Z ::
    forall (f :: k -> *) x y zs.
    Prism (NS f (x ': zs)) (NS f (y ': zs)) (f x) (f y)
_Z = prism Z p
  where
    p :: NS f (x ': zs) -> Either (NS f (y ': zs)) (f x)
    p (Z x)  = Right x
    p (S xs) = Left (S xs)

_S ::
    forall (f :: k -> *) x ys zs.
    Prism (NS f (x ': ys)) (NS f (x ': zs)) (NS f ys) (NS f zs)
_S = prism S p
  where
    p :: NS f (x ': ys) -> Either (NS f (x ': zs)) (NS f ys)
    p (Z x)  = Left $ Z x
    p (S xs) = Right $ xs

-------------------------------------------------------------------------------
-- DatatypeInfo
-------------------------------------------------------------------------------

moduleName :: Lens' (DatatypeInfo xss) ModuleName
moduleName = lens g s
  where
    g :: DatatypeInfo xss -> ModuleName
#if MIN_VERSION_generics_sop(0,5,0)
    g (ADT m _ _ _)   = m
#else
    g (ADT m _ _)     = m
#endif
    g (Newtype m _ _) = m

    s :: DatatypeInfo xss -> ModuleName -> DatatypeInfo xss
#if MIN_VERSION_generics_sop(0,5,0)
    s (ADT _ n cs ss) m = ADT m n cs ss
#else
    s (ADT _ n cs)    m = ADT m n cs
#endif
    s (Newtype _ n c) m = Newtype m n c

datatypeName :: Lens' (DatatypeInfo xss) DatatypeName
datatypeName = lens g s
  where
    g :: DatatypeInfo xss -> DatatypeName
#if MIN_VERSION_generics_sop(0,5,0)
    g (ADT _ n _ _)   = n
#else
    g (ADT _ n _)     = n
#endif
    g (Newtype _ n _) = n

    s :: DatatypeInfo xss -> DatatypeName -> DatatypeInfo xss
#if MIN_VERSION_generics_sop(0,5,0)
    s (ADT m _ cs ss) n = ADT m n cs ss
#else
    s (ADT m _ cs)    n = ADT m n cs
#endif
    s (Newtype m _ c) n = Newtype m n c

constructorInfo :: Lens' (DatatypeInfo xss) (NP ConstructorInfo xss)
constructorInfo = lens g s
  where
    g :: DatatypeInfo xss -> NP ConstructorInfo xss
#if MIN_VERSION_generics_sop(0,5,0)
    g (ADT _ _ cs _)  = cs
#else
    g (ADT _ _ cs)    = cs
#endif
    g (Newtype _ _ c) = c :* Nil

    s :: DatatypeInfo xss -> NP ConstructorInfo xss -> DatatypeInfo xss
#if MIN_VERSION_generics_sop(0,5,0)
    s (ADT m n _ ss)  cs          = ADT m n cs ss
#else
    s (ADT m n _)     cs          = ADT m n cs
#endif
    s (Newtype m n _) (c :* Nil)  = Newtype m n c
#if __GLASGOW_HASKELL__ < 800
    s _ _ = error "constructorInfo set: impossible happened"
#endif

-- | /Note:/ 'Infix' constructor has operator as a 'ConstructorName'. Use as
-- setter with care.
constructorName :: Lens' (ConstructorInfo xs) ConstructorName
constructorName f (Constructor n      ) = (\ n' -> Constructor n'      ) `fmap` f n
constructorName f (Infix       n a fix) = (\ n' -> Infix       n' a fix) `fmap` f n
constructorName f (Record      n finfo) = (\ n' -> Record      n' finfo) `fmap` f n

#if MIN_VERSION_generics_sop(0,5,0)
-- | Strictness info is only aviable for 'ADT' data. This combinator is available only with @generics-sop@ 0.5 or later.
strictnessInfo :: Traversal' (DatatypeInfo xss) (POP StrictnessInfo xss)
strictnessInfo _ di@(Newtype {}) = pure di
strictnessInfo f (ADT m n cs ss) = ADT m n cs <$> f ss
#endif
