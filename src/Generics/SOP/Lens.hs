{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}
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
    rep,
    -- * SOP & POP
    sop, pop,
    unsop, unpop,
    -- * Functors
    isoI, isoK,
    uni, unk,
    -- * Products
    singletonP,
    unSingletonP,
    headLens,
    tailLens,
    -- * Sums
    singletonS,
    unSingletonS,
    _Z,
    _S,
    -- * DatatypeInfo
    datatypeName,
    constructorInfo,
    ) where

import Control.Lens
import Generics.SOP hiding (from)
import qualified Generics.SOP as SOP

rep :: Generic a => Iso' a (Rep a)
rep = iso SOP.from SOP.to

-------------------------------------------------------------------------------
-- SOP & POP
-------------------------------------------------------------------------------

sop ::
    forall (f :: k -> *) xss yss.
    Iso (NS (NP f) xss) (NS (NP f) yss) (SOP f xss) (SOP f yss)
sop = iso SOP unSOP

unsop ::
    forall (f :: k -> *) xss yss.
    Iso (SOP f xss) (SOP f yss) (NS (NP f) xss) (NS (NP f) yss)
unsop = from sop

pop ::
    forall (f :: k -> *) xss yss.
    Iso (NP (NP f) xss) (NP (NP f) yss) (POP f xss) (POP f yss)
pop = iso POP unPOP

unpop ::
    forall (f :: k -> *) xss yss.
    Iso (POP f xss) (POP f yss) (NP (NP f) xss) (NP (NP f) yss)
unpop = from pop

instance (t ~ SOP f xss) => Rewrapped (SOP f xss) t
instance Wrapped (SOP f xss) where
    type Unwrapped (SOP f xss) = NS (NP f) xss
    _Wrapped' = from sop

instance (t ~ POP f xss) => Rewrapped (POP f xss) t
instance Wrapped (POP f xss) where
    type Unwrapped (POP f xss) = NP (NP f) xss
    _Wrapped' = from pop

-------------------------------------------------------------------------------
-- Basic functors
-------------------------------------------------------------------------------

isoI :: Iso a b (I a) (I b)
isoI = iso I unI

uni :: Iso (I a) (I b) a b
uni = iso unI I

isoK :: Iso a b (K a c) (K b c)
isoK = iso K unK

unk :: Iso (K a c) (K b c) a b
unk = iso unK K

instance (t ~ I a) => Rewrapped (I a) t
instance Wrapped (I a) where
    type Unwrapped (I a) = a
    _Wrapped' = from isoI

instance (t ~ K a b) => Rewrapped (K a b) t
instance Wrapped (K a b) where
    type Unwrapped (K a b) = a
    _Wrapped' = from isoK

-------------------------------------------------------------------------------
-- Products
-------------------------------------------------------------------------------

singletonP ::
    forall (f :: k -> *) x y.
    Iso (f x) (f y) (NP f '[x]) (NP f '[y])
singletonP = iso s g
  where
    g :: NP f '[y] -> f y
    g (y  :* Nil)   = y
#if __GLASGOW_HASKELL < 800
    g _ = error "singletonP"
#endif

    s :: f x -> NP f '[x]
    s x = x :* Nil

unSingletonP ::
    forall (f :: k -> *) x y.
    Iso (NP f '[x]) (NP f '[y]) (f x) (f y)
unSingletonP = from singletonP

headLens ::
    forall (f :: k -> *) x y zs.
    Lens (NP f (x ': zs)) (NP f (y ': zs)) (f x) (f y)
headLens = lens g s
  where
    g :: NP f (x ': zs) -> f x
    g (x  :* _zs)   = x

    s :: NP f (x ': zs) -> f y -> NP f (y ': zs)
    s (_x :*  zs) y = y :* zs

tailLens ::
    forall (f :: k -> *) x ys zs.
    Lens (NP f (x ': ys)) (NP f (x ': zs)) (NP f ys) (NP f zs)
tailLens = lens g s
  where
    g :: NP f (x ': ys) -> NP f ys
    g (_x :*  ys)    = ys

    s :: NP f (x ': ys) -> NP f zs -> NP f (x ': zs)
    s (x  :* _ys) zs = x :* zs

instance Field1 (NP f (x ': zs)) (NP f (y ': zs)) (f x) (f y) where _1 = headLens
instance Field1 (POP f (x ': zs)) (POP f (y ': zs)) (NP f x) (NP f y) where _1 = from pop . _1

instance Field2 (NP f (a ': x ': zs)) (NP f (a ': y ': zs)) (f x) (f y) where _2 = tailLens . _1
instance Field2 (POP f (a ': x ': zs)) (POP f (a ': y ': zs)) (NP f x) (NP f y) where _2 = from pop . _2

instance Field3 (NP f (a ': b ': x ': zs)) (NP f (a ': b ': y ': zs)) (f x) (f y) where _3 = tailLens . _2
instance Field3 (POP f (a ': b ': x ': zs)) (POP f (a ': b ': y ': zs)) (NP f x) (NP f y) where _3 = from pop . _3

instance Field4 (NP f (a ': b ': c ': x ': zs)) (NP f (a ': b ': c ': y ': zs)) (f x) (f y) where _4 = tailLens . _3
instance Field4 (POP f (a ': b ': c ': x ': zs)) (POP f (a ': b ': c ': y ': zs)) (NP f x) (NP f y) where _4 = from pop . _4

instance Field5 (NP f (a ': b ': c ': d ': x ': zs)) (NP f (a ': b ': c ': d ': y ': zs)) (f x) (f y) where _5 = tailLens . _4
instance Field5 (POP f (a ': b ': c ': d ': x ': zs)) (POP f (a ': b ': c ': d ': y ': zs)) (NP f x) (NP f y) where _5 = from pop . _5

instance Field6 (NP f (a ': b ': c ': d ': e ': x ': zs)) (NP f (a ': b ': c ': d ': e ': y ': zs)) (f x) (f y) where _6 = tailLens . _5
instance Field6 (POP f (a ': b ': c ': d ': e ': x ': zs)) (POP f (a ': b ': c ': d ': e ': y ': zs)) (NP f x) (NP f y) where _6 = from pop . _6

instance Field7 (NP f' (a ': b ': c ': d ': e ': f ': x ': zs)) (NP f' (a ': b ': c ': d ': e ': f ': y ': zs)) (f' x) (f' y) where _7 = tailLens . _6
instance Field7 (POP f' (a ': b ': c ': d ': e ': f ': x ': zs)) (POP f' (a ': b ': c ': d ': e ': f ': y ': zs)) (NP f' x) (NP f' y) where _7 = from pop . _7

instance Field8 (NP f' (a ': b ': c ': d ': e ': f ': g ': x ': zs)) (NP f' (a ': b ': c ': d ': e ': f ': g ': y ': zs)) (f' x) (f' y) where _8 = tailLens . _7
instance Field8 (POP f' (a ': b ': c ': d ': e ': f ': g ': x ': zs)) (POP f' (a ': b ': c ': d ': e ': f ': g ': y ': zs)) (NP f' x) (NP f' y) where _8 = from pop . _8

instance Field9 (NP f' (a ': b ': c ': d ': e ': f ': g ': h ': x ': zs)) (NP f' (a ': b ': c ': d ': e ': f ': g ': h ': y ': zs)) (f' x) (f' y) where _9 = tailLens . _8
instance Field9 (POP f' (a ': b ': c ': d ': e ': f ': g ': h ': x ': zs)) (POP f' (a ': b ': c ': d ': e ': f ': g ': h ': y ': zs)) (NP f' x) (NP f' y) where _9 = from pop . _9

-------------------------------------------------------------------------------
-- Sums
-------------------------------------------------------------------------------

singletonS ::
    forall (f :: k -> *) x y.
    Iso (f x) (f y) (NS f '[x]) (NS f '[y])
singletonS = iso s g
  where
    g :: NS f '[y] -> f y
    g (Z y)   = y
#if __GLASGOW_HASKELL < 800
    g _ = error "singletonS"
#endif

    s :: f x -> NS f '[x]
    s x = Z x

unSingletonS ::
    forall (f :: k -> *) x y.
    Iso (NS f '[x]) (NS f '[y]) (f x) (f y)
unSingletonS = from singletonS

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

datatypeName :: Lens' (DatatypeInfo xss) DatatypeName
datatypeName = lens g s
  where
    g :: DatatypeInfo xss -> DatatypeName
    g (ADT _ n _)     = n
    g (Newtype _ n _) = n

    s :: DatatypeInfo xss -> DatatypeName -> DatatypeInfo xss
    s (ADT m _ cs)    n = ADT m n cs
    s (Newtype m _ c) n = Newtype m n c

constructorInfo :: Lens' (DatatypeInfo xss) (NP ConstructorInfo xss)
constructorInfo = lens g s
  where
    g :: DatatypeInfo xss -> NP ConstructorInfo xss
    g (ADT _ _ cs)    = cs
    g (Newtype _ _ c) = c :* Nil

    s :: DatatypeInfo xss -> NP ConstructorInfo xss -> DatatypeInfo xss
    s (ADT m n _)     cs          = ADT m n cs
    s (Newtype m n _) (c :* Nil)  = Newtype m n c
    s _ _ = error "constructorInfo set: impossible happened"
