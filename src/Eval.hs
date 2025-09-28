{-# LANGUAGE OverloadedStrings #-}
-- for the implementation of costrong
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Eval where

import Data.Functor.Foldable
import Data.String
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Types


data Val
  = VPair Val Val
  | VInl Val
  | VInr Val
  | VLit Lit
  | VFunc (Val -> Val)


instance Pretty Val where
  pPrint (VPair x y) = prettyTuple [x, y]
  -- TODO(sandy): stupid, should do assoc
  pPrint (VInl x) = parens $ "inl" <+> pPrint x
  pPrint (VInr x) = parens $ "inr" <+> pPrint x
  pPrint (VLit x) = pPrint x
  pPrint (VFunc _) = "<fn>"


instance IsString Val where
  fromString = VLit . fromString


eval :: Expr a -> Val
eval Inl = VFunc VInl
eval Inr = VFunc VInr
eval Proj1 = VFunc $
  \case
    VPair x _ -> x
    _ -> error "projection of a nonpair"
eval Proj2 = VFunc $
  \case
    VPair _ y -> y
    _ -> error "projection of a nonpair"
eval Dist = VFunc $
  \case
    VPair (VInl a) c -> VInl (VPair a c)
    VPair (VInr b) c -> VInr (VPair b c)
    _ -> error "distrib of a nonpair"
eval (Var _) = error "var!"
eval (Lit l) = VFunc $ const $ VLit l
eval (App (eval -> VFunc f) (eval -> a)) = f a
eval App {} = error "bad app"
eval (AndThen (eval -> VFunc f) (eval -> VFunc g)) = VFunc (g . f)
eval AndThen {} = error "bad then"
eval (Fork (eval -> VFunc f) (eval -> VFunc g)) = VFunc $ \a -> VPair (f a) (g a)
eval Fork {} = error "bad fork"
eval (Join (eval -> VFunc f) (eval -> VFunc g)) =
  VFunc $ \case
    VInl a -> f a
    VInr a -> g a
    z -> error $ "join of a nonsum: " <> show (pPrint z)
eval Join {} = error "bad join"
eval Id = VFunc id
eval (Cochoice (eval -> VFunc f)) =
  VFunc $
    let go i =
          case f i of
            VInl a -> a
            o@VInr {} -> go o
            _ -> error "cochoice of a noncoprod"
     in go . VInl
eval Cochoice {} = error "bad cochoice"
eval (Costrong (eval -> VFunc f)) =
  VFunc $ \a ->
    let ~(VPair b x) = f (VPair a x)
     in b
eval Costrong {} = error "bad strong"
eval (Prim Add) = VFunc $ \(VPair (VLit (Int a)) (VLit (Int b))) -> VLit $ Int $ a + b
eval (Prim Sub) = VFunc $ \(VPair (VLit (Int a)) (VLit (Int b))) -> VLit $ Int $ a - b
eval (Prim Abs) = VFunc $ \(VLit (Int a)) ->
  case a < 0 of
    True -> VInl $ VLit $ Int $ abs a
    False -> VInr $ VLit $ Int a


mkPair :: [Val] -> Val
mkPair = foldr1 VPair


inline :: (a -> Expr a) -> Expr a -> Expr a
inline f = cata $ \case
  VarF a -> f a
  x -> embed x
