{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module
    Control.Arrow.CategoryDef
where

import qualified Prelude hiding (fst, snd)
import qualified Control.Category as A
import qualified Control.Arrow as A

import Control.Categorical.Bifunctor
import Control.Categorical.Object
import Control.Category.Associative
import Control.Category.Braided
import Control.Category.Cartesian
import Control.Category.Distributive
import Control.Category.Monoidal

class A.Arrow k => CategoryDef k where {}

-- (,) Part
instance {-# Overlaps #-}
    CategoryDef k =>
    PFunctor (,) k k
  where
    first = A.first

instance {-# Overlaps #-}
    CategoryDef k =>
    QFunctor (,) k k
  where
    second = A.second

instance {-# Overlaps #-}
    CategoryDef k =>
    Bifunctor (,) k k k
  where
    bimap = (A.***)

instance {-# Overlaps #-}
    CategoryDef k =>
    Associative k (,)
  where
    associate = A.arr associate
    disassociate = A.arr disassociate

instance {-# Overlaps #-}
    CategoryDef k =>
    Braided k (,)
  where
    braid = A.arr braid

instance {-# Overlaps #-}
    CategoryDef k =>
    Symmetric k (,) where {}

instance {-# Overlaps #-}
    CategoryDef k =>
    Monoidal k (,)
  where
    type Id k (,) = ()
    idl = A.arr idl
    idr = A.arr idr
    coidl = A.arr coidl
    coidr = A.arr coidr

instance {-# Overlaps #-}
    CategoryDef k =>
    Cartesian k
  where
    type Product k = (,)
    fst = A.arr fst
    snd = A.arr snd
    (&&&) = (A.&&&)

