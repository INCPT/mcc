{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module OSC.Pretty where

import GHC.Generics

import Prettyprinter

class GPretty f where
  gpretty :: f p -> Doc ann

instance (GPretty a, GPretty b) => GPretty (a :+: b) where
  gpretty (L1 x) = gpretty x
  gpretty (R1 x) = gpretty x

instance (GPretty a) => GPretty (M1 D c a) where
  gpretty (M1 x) = gpretty x

instance (GPretty a) => GPretty (M1 C c a) where
  gpretty (M1 x) = gpretty x

instance (Pretty c) => GPretty (M1 S m (K1 R c)) where
  gpretty (M1 (K1 x)) = pretty x

genPretty :: (Generic a, GPretty (Rep a)) => a -> Doc ann
genPretty x = gpretty (from x)