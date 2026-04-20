{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module OSC.Pretty where

import GHC.Generics

import Data.Text (Text)

import Prettyprinter
import Prettyprinter.Render.String
import Prettyprinter.Render.Text

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

genPrettyString :: (Generic a, GPretty (Rep a)) => a -> String
genPrettyString = renderString . layoutPretty defaultLayoutOptions . genPretty

genPrettyText :: (Generic a, GPretty (Rep a)) => a -> Text
genPrettyText = renderStrict . layoutPretty defaultLayoutOptions . genPretty

prettyString :: Pretty a => a -> String
prettyString = renderString . layoutPretty defaultLayoutOptions . pretty

prettyText :: Pretty a => a -> Text
prettyText = renderStrict . layoutPretty defaultLayoutOptions . pretty