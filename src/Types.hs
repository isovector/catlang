{-# LANGUAGE BlockArguments       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Types where

import Data.Char (toUpper)
import Data.Data
import Data.Functor.Foldable.TH
import Data.String
import Numeric.Natural
import Text.PrettyPrint.HughesPJClass hiding ((<>), Str)
import Text.Read (readMaybe)


instance Pretty Natural where
  pPrint = text . show



data Expr a
  = Var !a
  | Lit Lit
  | App (Expr a) (Expr a)
  | AndThen (Expr a) (Expr a)
  | Fork (Expr a) (Expr a)
  | Join (Expr a) (Expr a)
  | Inl                -- ^ a ~> a + b
  | Inr                -- ^ b ~> a + b
  | Proj1              -- ^ a * b ~> a
  | Proj2              -- ^ a * b ~> b
  | Id                 -- ^ a ~> a
  | Dist               -- ^ (a + b) * c ~> a * c + b * c
  | Costrong (Expr a)  -- ^ (a * x ~> b * x) -> (a ~> b)
  | Cochoice (Expr a)  -- ^ (a + x ~> b + x) -> (a ~> b)
  deriving stock (Eq, Ord, Show, Read, Functor, Foldable, Traversable, Data, Typeable)

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

  pPrintPrec l p (Var a) =
    maybeParens (p >= 10) $
      "call" <+> pPrintPrec l 10 a
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
  pPrintPrec _ _ Inl   = "inl"
  pPrintPrec _ _ Inr   = "inr"
  pPrintPrec _ _ Proj1 = "prj₁"
  pPrintPrec _ _ Proj2 = "prj₂"
  pPrintPrec _ _ Id    = "id"
  pPrintPrec _ _ Dist  = "dist"
  pPrintPrec _ _ Id    = "id"
  pPrintPrec l _ (Costrong f) =
    parens $
      "costrong" <+> pPrintPrec l 10 f
  pPrintPrec l _ (Cochoice f) =
    parens $
      "cochoice" <+> pPrintPrec l 10 f

instance (IsString a, Read a) => IsString (Expr a) where
  fromString s =
    case readMaybe $ mapFirst toUpper s of
      Just p -> p
      Nothing -> Var $ fromString s

pattern Push :: Expr a -> Expr a
pattern Push f = Fork f Id

pattern Index :: Int -> Expr a
pattern Index n <- (countNs -> Just n)
  where Index n = foldr AndThen (Proj1) $ replicate n $ Proj2

pattern (:.) :: Expr a -> Expr a -> Expr a
pattern (:.)f g <- (split -> (f, g))
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
  | NatTy
  deriving stock (Eq, Ord, Show, Data, Typeable)

instance Pretty LitTy where
  pPrint StrTy = "String"
  pPrint CharTy = "Char"
  pPrint NatTy = "Nat"

data Lit
  = Str String
  | Char Char
  | Nat Natural
  deriving stock (Eq, Ord, Show, Read, Data, Typeable)

instance Pretty Lit where
  pPrint (Str s) = pPrint s
  pPrint (Char c) = pPrint c
  pPrint (Nat i) = pPrint i

instance IsString Lit where
  fromString = Str


data Stmt a
  = Run (Cmd a)
  | Bind a (Cmd a)
  | More (Stmt a) (Stmt a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Pretty a => Pretty (Stmt a) where
  pPrint (Run c) = pPrint c
  pPrint (Bind a c) =
    hang (pPrint a) 2 $ "<—" <> pPrint c
  pPrint (More a b) = pPrint a $$ pPrint b


data Cmd a
  = Do (Expr a) [a]
  | Case a (a, Stmt a) (a, Stmt a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Pretty a => Pretty (Cmd a) where
  pPrint (Do e as) =
    (pPrint e <> "—<") <+> prettyTuple as
  pPrint (Case a (x, l) (y, r)) =
    hang ("case" <+> pPrint a <+> "of") 2 $ vcat
      [ hang ("inl" <+> pPrint x <+> "→") 2 $ pPrint l
      , hang ("inr" <+> pPrint y <+> "→") 2 $ pPrint r
      ]


prettyTuple :: Pretty a => [a] -> Doc
prettyTuple [x] = pPrint x
prettyTuple xs = parens $ hsep $ punctuate "," $ fmap pPrint xs


data TopDecl a
  = AnonArrow
      a  -- ^ Input name
      (Stmt a)

instance Pretty a => Pretty (TopDecl a) where
  pPrint (AnonArrow a b) =
    hang (pPrint a <+> "→") 2 $ pPrint b


makeBaseFunctor [''Expr, ''Lit, ''Stmt, ''Cmd]

deriving stock instance (Show a, Show x) => Show (ExprF a x)


(@@) :: Expr a -> Expr a -> Expr a
(@@) f a = App f a
infixl 1 @@
