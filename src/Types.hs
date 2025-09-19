{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Types where

import           Data.Char (toUpper)
import           Data.Data
import           Data.Functor.Foldable.TH
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.String
import           Text.PrettyPrint.HughesPJClass hiding ((<>), Str)
import           Text.Read (readMaybe)


data Prim
  = Inl    -- ^ a -> a + b
  | Inr    -- ^ b -> a + b
  | Proj1  -- ^ a * b -> a
  | Proj2  -- ^ a * b -> b
  | Id     -- ^ a -> a
  | Dist   -- ^ (a + b) * c -> a * c + b * c
  deriving stock (Eq, Ord, Show, Read, Data, Typeable)


instance Pretty Prim where
  pPrint Inl   = "inl"
  pPrint Inr   = "inr"
  pPrint Proj1 = "prj₁"
  pPrint Proj2 = "prj₂"
  pPrint Id    = "id"
  pPrint Dist  = "dist"


data Expr a
  = Var a
  | Prim Prim
  | Lit Lit
  | App (Expr a) (Expr a)
  | AndThen (Expr a) (Expr a)
  | Fork (Expr a) (Expr a)
  | Join (Expr a) (Expr a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Pretty a => Pretty (Expr a) where
  pPrintPrec l p (Index n) =
    maybeParens (p >= 10) $
      "idx" <+> pPrintPrec l p n
  pPrintPrec l p (Push f :. Prim Dist :. k) =
    maybeParens (p >= 3) $
      ("branch" <+> pPrintPrec l 10 f) <+> "⨟" <+> pPrintPrec l 2 k
  pPrintPrec l p (Push f) =
    maybeParens (p >= 10) $
      "push" <+> pPrintPrec l 10 f

  pPrintPrec l p (Var a) =
    maybeParens (p >= 10) $
      "call" <+> pPrintPrec l 10 a
  pPrintPrec l p (Prim pr) = pPrintPrec l p pr
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

instance IsString a => IsString (Expr a) where
  fromString s =
    case readMaybe $ mapFirst toUpper s of
      Just p -> Prim p
      Nothing -> Var $ fromString s

pattern Push :: Expr a -> Expr a
pattern Push f = Fork f (Prim Id)

pattern Index :: Int -> Expr a
pattern Index n <- (countNs -> Just n)
  where Index n = foldr AndThen (Prim Proj1) $ replicate n $ Prim Proj2

pattern (:.) :: Expr a -> Expr a -> Expr a
pattern (:.)f g <- (split -> (f, g))
  where
    (:.) f (Prim Id) = f
    (:.) (Prim Id) f = f
    (:.) f g = AndThen f g
infixr 0 :.


split :: Expr a -> (Expr a, Expr a)
split (AndThen (AndThen f g) h) = fmap (flip AndThen $ AndThen g h) $ split f
split (AndThen f g) = (f, g)
split x = (x, Prim Id)

countNs :: Expr a -> Maybe Int
countNs (Prim Proj2 :. e) = fmap (+ 1) $ countNs e
countNs (Prim Proj1) = Just 0
countNs _ = Nothing


mapFirst :: (Char -> Char) -> String -> String
mapFirst _ [] = []
mapFirst f (c : cs) = f c : cs


data Lit
  = Unit
  | Str String
  | Char Char
  | Num Integer
  deriving stock (Eq, Ord, Show, Data, Typeable)

instance Pretty Lit where
  pPrint Unit = "!"
  pPrint (Str s) = pPrint s
  pPrint (Char c) = pPrint c
  pPrint (Num i) = pPrint i

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


data Constraint
  = Cartesian
  | Cocartesian
  | Terminal
  | Initial
  | LitStr
  | LitChar
  | LitNum
  deriving stock (Eq, Ord, Show, Data, Typeable)


data TopDecl a
  = AnonArrow
      a  -- ^ Input name
      (Stmt a)

instance Pretty a => Pretty (TopDecl a) where
  pPrint (AnonArrow a b) =
    hang (pPrint a <+> "→") 2 $ pPrint b


makeBaseFunctor [''Prim, ''Expr, ''Lit, ''Stmt, ''Constraint, ''Cmd]


primConstraints :: Data a => a -> Set Constraint
primConstraints = everything (<>) $
  mkQ mempty \case
    Inl -> S.singleton Cocartesian
    Inr -> S.singleton Cocartesian
    Proj1 -> S.singleton Cartesian
    Proj2 -> S.singleton Cartesian
    Id -> mempty
    Dist -> S.fromList [Cartesian, Cocartesian]
  `extQ` \case
    Unit -> S.singleton Terminal
    Str{} -> S.singleton LitStr
    Char{} -> S.singleton LitChar
    Num{} -> S.singleton LitNum


(@@) :: Expr a -> Expr a -> Expr a
(@@) f a = App f a
infixl 1 @@
