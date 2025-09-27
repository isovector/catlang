{-# LANGUAGE TemplateHaskell #-}

module Backend.TH where

import Language.Haskell.TH.Syntax
import Prelude hiding (id, (.))
import Language.Haskell.TH
import Control.Category
import Control.Category.Cartesian
import Control.Category.Monoidal
import Control.Category.Recursive
import Types
import Data.Functor.Foldable

class (MonoidalProduct k, MonoidalSum k) => Distrib k where
  distribute :: (Either a b, c) `k` Either (a, c) (b, c)

instance Distrib (->) where
  distribute (Left a, c) = Left (a, c)
  distribute (Right b, c) = Right (b, c)

toCategory :: Expr Name -> Q Exp
toCategory = cata $ \case
  VarF v -> varE v
  AppF f a -> appE f a
  AndThenF f g -> appsE [varE '(>>>), f, g]
  ForkF f g -> appsE [varE '(&&&), f, g]
  JoinF f g -> appsE [varE '(|||), f, g]
  InlF -> varE 'injectL
  InrF -> varE 'injectR
  Proj1F -> varE 'fst'
  Proj2F -> varE 'snd'
  IdF -> varE 'id
  DistF -> varE 'distribute
  CostrongF f -> appE (varE 'fixL) f
  CochoiceF f -> appE (varE 'recurseL) f
  LitF (Int x) -> appE (varE 'const) $ lift x
  LitF (Str x) -> appE (varE 'const) $ lift x
  LitF (Char x) -> appE (varE 'const) $ lift x
  PrimF Add -> [| uncurry (+) |]
  PrimF Sub -> [| uncurry (-) |]
  PrimF Abs ->
    [| \x -> case x < 0 of
         True -> Left (abs x)
         False -> Right x
    |]

