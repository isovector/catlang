{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Types where

import Data.Char (toUpper)
import Data.Functor.Foldable.TH
import Data.String
import Numeric.Natural
import Text.PrettyPrint.HughesPJClass hiding (Str, (<>))
import Text.Read (readMaybe)


instance Pretty Natural where
  pPrint = text . show


data Prim
  = Add
  | Sub
  | Abs -- Int → Int + Int, returning inl (abs) if the input was negative, otherwise inr
  deriving stock (Eq, Ord, Show, Read)


data Type
  = Prod Type Type
  | Coprod Type Type
  | Arr Type Type
  | TyCon LitTy
  | TyVar String
  deriving stock (Eq, Ord, Show)


instance Pretty Type where
  pPrintPrec l p (Prod x y) =
    maybeParens (p > 5) $
      pPrintPrec l 6 x <+> "×" <+> pPrintPrec l 6 y
  pPrintPrec l p (Coprod x y) =
    maybeParens (p > 3) $
      pPrintPrec l 4 x <+> "+" <+> pPrintPrec l 4 y
  pPrintPrec l p (Arr x y) =
    maybeParens (p > 0) $
      pPrintPrec l 1 x <+> "→" <+> pPrintPrec l 0 y
  pPrintPrec _ _ (TyCon t) = pPrint t
  pPrintPrec _ _ (TyVar t) = text t


data Expr a
  = Var !a
  | Lit Lit
  | App (Expr a) (Expr a)
  | AndThen (Expr a) (Expr a)
  | Fork (Expr a) (Expr a)
  | Join (Expr a) (Expr a)
  | -- | a ~> a + b
    Inl
  | -- | b ~> a + b
    Inr
  | -- | a * b ~> a
    Proj1
  | -- | a * b ~> b
    Proj2
  | -- | a ~> a
    Id
  | -- | (a + b) * c ~> a * c + b * c
    Dist
  | -- | (a * x ~> b * x) -> (a ~> b)
    Costrong (Expr a)
  | -- | (a + x ~> b + x) -> (a ~> b)
    Cochoice (Expr a)
  | Prim Prim
  deriving stock (Eq, Ord, Show, Read, Functor, Foldable, Traversable)


instance Pretty a => Pretty (Expr a) where
  -- pPrintPrec l p (Index n) =
  --   maybeParens (p >= 10) $
  --     "idx" <+> pPrintPrec l p n
  -- pPrintPrec l p (Push f :. Dist :. k) =
  --   maybeParens (p >= 3) $
  --     ("branch" <+> pPrintPrec l 10 f) <+> "⨟" <+> pPrintPrec l 2 k
  -- pPrintPrec l p (Push f) =
  --   maybeParens (p >= 10) $
  --     "push" <+> pPrintPrec l 10 f

  pPrintPrec _ _ (Var a) =
    "ref:" <> pPrint a
  pPrintPrec l p (Lit pr) = pPrintPrec l p pr
  pPrintPrec l p (App f a) =
    maybeParens (p >= 10) $
      hang (pPrintPrec l 9 f) 2 $
        pPrintPrec l 10 a
  pPrintPrec l p (AndThen f g) =
    maybeParens (p >= 3) $
      pPrintPrec l 2 f <+> "⨟" <+> pPrintPrec l 2 g
  pPrintPrec l p (Fork f g) =
    maybeParens (p >= 4) $
      pPrintPrec l 4 f <+> "△" <+> pPrintPrec l 4 g
  pPrintPrec l p (Join f g) =
    maybeParens (p >= 5) $
      pPrintPrec l 5 f <+> "▽" <+> pPrintPrec l 5 g
  pPrintPrec _ _ Inl = "inl"
  pPrintPrec _ _ Inr = "inr"
  pPrintPrec _ _ Proj1 = "prj₁"
  pPrintPrec _ _ Proj2 = "prj₂"
  pPrintPrec _ _ Id = "id"
  pPrintPrec _ _ Dist = "dist"
  pPrintPrec l _ (Costrong f) =
    parens $
      "costrong" <+> pPrintPrec l 10 f
  pPrintPrec l _ (Cochoice f) =
    parens $
      "cochoice" <+> pPrintPrec l 10 f
  pPrintPrec _ _ (Prim Add) = "(+)"
  pPrintPrec _ _ (Prim Sub) = "(-)"
  pPrintPrec _ _ (Prim Abs) = "abs"


instance (IsString a, Read a) => IsString (Expr a) where
  fromString s =
    case readMaybe $ mapFirst toUpper s of
      Just p -> p
      Nothing -> Var $ fromString s


pattern Push :: Expr a -> Expr a
pattern Push f = Fork f Id


pattern Index :: Int -> Expr a
pattern Index n <- (countNs -> Just n)
  where
    Index n = foldr AndThen (Proj1) $ replicate n $ Proj2


pattern (:.) :: Expr a -> Expr a -> Expr a
pattern (:.) f g <- (split -> (f, g))
  where
    (:.) f Id = f
    (:.) Id f = f
    (:.) f g = AndThen f g
infixr 0 :.


split :: Expr a -> (Expr a, Expr a)
split (AndThen (AndThen f g) h) = fmap (flip AndThen $ AndThen g h) $ split f
split (AndThen f g) = (f, g)
split x = (x, Id)


countNs :: Expr a -> Maybe Int
countNs (Proj2 :. e) = fmap (+ 1) $ countNs e
countNs (Proj1) = Just 0
countNs _ = Nothing


mapFirst :: (Char -> Char) -> String -> String
mapFirst _ [] = []
mapFirst f (c : cs) = f c : cs


data LitTy
  = StrTy
  | CharTy
  | IntTy
  deriving stock (Eq, Ord, Show)


instance Pretty LitTy where
  pPrint StrTy = "String"
  pPrint CharTy = "Char"
  pPrint IntTy = "Int"


data Lit
  = Str String
  | Char Char
  | Int Int
  deriving stock (Eq, Ord, Show, Read)


instance Pretty Lit where
  pPrint (Str s) = pPrint s
  pPrint (Char c) = pPrint c
  pPrint (Int i) = pPrint i


instance IsString Lit where
  fromString = Str


data Pat a
  = PVar a
  | PPair (Pat a) (Pat a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)


instance Pretty a => Pretty (Pat a) where
  pPrint (PVar a) = pPrint a
  pPrint (PPair a b) = parens $ pPrint a <> ("," <+> pPrint b)


instance IsString a => IsString (Pat a) where
  fromString = PVar . fromString


data Stmt a
  = Run (Cmd a)
  | Bind (Pat a) (Cmd a)
  | More (Stmt a) (Stmt a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)


instance Pretty a => Pretty (Stmt a) where
  pPrint (Run c) = pPrint c
  pPrint (Bind a (Do Id args)) =
    hang ("let" <+> pPrint a <+> "=") 2 $
      pPrint args
  pPrint (Bind a c) =
    hang (pPrint a) 2 $ "<—" <> pPrint c
  pPrint (More a b) = pPrint a $$ pPrint b


data Cmd a
  = Do (Expr a) (Pat a)
  | Case a (Pat a, Stmt a) (Pat a, Stmt a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)


instance Pretty a => Pretty (Cmd a) where
  pPrint (Do e as) =
    (pPrint e <> "—<") <+> pPrint as
  pPrint (Case a (x, l) (y, r)) =
    hang ("case" <+> pPrint a <+> "of") 2 $
      vcat
        [ hang ("inl" <+> pPrint x <+> "→") 2 $ pPrint l
        , hang ("inr" <+> pPrint y <+> "→") 2 $ pPrint r
        ]


prettyTuple :: Pretty a => [a] -> Doc
prettyTuple [x] = pPrint x
prettyTuple xs = parens $ hsep $ punctuate "," $ fmap pPrint xs


data TopDecl a
  = AnonArrow
      a
      -- ^ Input name
      (Stmt a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)


instance Pretty a => Pretty (TopDecl a) where
  pPrint (AnonArrow a b) =
    hang (pPrint a <+> "→") 2 $ pPrint b


makeBaseFunctor [''Expr, ''Lit, ''Stmt, ''Cmd, ''Type, ''Pat]


deriving stock instance (Show a, Show x) => Show (ExprF a x)


(@@) :: Expr a -> Expr a -> Expr a
(@@) f a = App f a
infixl 1 @@
