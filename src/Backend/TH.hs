{-# LANGUAGE TemplateHaskell #-}

module Backend.TH where

import Control.Category
import Control.Category.Cartesian
import Control.Category.Monoidal
import Control.Category.Recursive
import Data.Functor.Foldable
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Types
import Prelude hiding (id, (.))


class (MonoidalProduct k, MonoidalSum k) => Distrib k where
  distribute :: (Either a b, c) `k` Either (a, c) (b, c)


instance Distrib (->) where
  distribute (Left a, c) = Left (a, c)
  distribute (Right b, c) = Right (b, c)

class IntLits k where
  intLit :: Int -> k a Int
  addPrim :: k (Int, Int) Int
  subPrim :: k (Int, Int) Int
  absPrim :: k Int (Either Int Int)


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
  LitF (Int x) -> appE (varE 'intLit) $ lift x
  LitF (Str x) -> [| str_lit $(lift x) |]
  LitF (Char x) -> [| char_lit $(lift x) |]
  PrimF Add -> varE 'addPrim
  PrimF Sub -> varE 'subPrim
  PrimF Abs -> varE 'absPrim
