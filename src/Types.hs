{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Types where

import Data.Functor.Foldable
import Prelude hiding (lookup)
import Data.Monoid
import qualified Data.Map as M
import Data.Map (Map)
import Control.Monad.Writer
import Control.Monad.Trans.State
import Data.Char (toUpper)
import Text.Read (readMaybe)
import Data.Generics.Schemes
import Data.Generics.Aliases
import qualified Data.Set as S
import Data.Set (Set)
import Data.Data
import Data.String
import Data.Functor.Foldable.TH

data Prim
  = Inl
  | Inr
  | Fork
  | Proj1
  | Proj2
  | Join
  | Nop
  deriving stock (Eq, Ord, Show, Read, Data, Typeable)

data Expr a
  = Var a
  | Prim Prim
  | Lit Lit
  | App (Expr a) (Expr a)
  | AndThen (Expr a) (Expr a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance IsString a => IsString (Expr a) where
  fromString s =
    case readMaybe $ mapFirst toUpper s of
      Just p -> Prim p
      Nothing -> Var $ fromString s

mapFirst :: (Char -> Char) -> String -> String
mapFirst _ [] = []
mapFirst f (c : cs) = f c : cs

data Lit
  = Unit
  | Str String
  | Char Char
  | Num Integer
  deriving stock (Eq, Ord, Show, Data, Typeable)

data Stmt a
  = Run (Expr a) [a]
  | Bind a (Expr a) [a]
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)



data Constraint
  = Cartesian
  | Cocartesian
  | Terminal
  | Initial
  | LitStr
  | LitChar
  | LitNum
  deriving stock (Eq, Ord, Show, Data, Typeable)

makeBaseFunctor [''Prim, ''Expr, ''Lit, ''Stmt, ''Constraint]


primConstraints :: Data a => a -> Set Constraint
primConstraints = everything (<>) $
  mkQ mempty \case
    Inl -> S.singleton Cocartesian
    Inr -> S.singleton Cocartesian
    Fork -> S.singleton Cocartesian
    Proj1 -> S.singleton Cartesian
    Proj2 -> S.singleton Cartesian
    Join -> S.singleton Cartesian
    Nop -> mempty
  `extQ` \case
    Unit -> S.singleton Terminal
    Str{} -> S.singleton LitStr
    Char{} -> S.singleton LitChar
    Num{} -> S.singleton LitNum


program :: [Stmt String]
program =
  [ Bind "x" "proj1" ["in"]
  , Bind "y" "proj2" ["in"]
  , Run "nop" ["y", "x"]
  ]

(@@) :: Expr a -> Expr a -> Expr a
(@@) f a = App f a
infixl 1 @@

desugared :: Expr String
desugared = quotient $ foldr AndThen "nop"
  [ "fork" @@ "proj1" @@ "nop"  -- ("x", in)
  , "fork" @@ AndThen "proj2" "proj2" @@ "nop"  -- ("y", ("x", in))
  , "fork" @@ "proj1" @@ AndThen "proj2" "proj1" -- ("y", "x")
  ]


newtype AllocM v a = AllocM { unAllocM :: StateT (Map v (Expr v)) (Writer [Expr v]) a }
  deriving newtype (Functor, Applicative, Monad)
  deriving (Semigroup, Monoid) via Ap (AllocM v) a

alloc :: Ord v => v -> Expr v -> AllocM v ()
alloc v e = AllocM $ do
  tell $ pure $ Prim Fork @@ e @@ Prim Nop
  -- succ everything in the context
  modify $ fmap $ AndThen $ Prim Proj2
  modify $ M.insert v $ Prim Proj1

lookup :: Ord v => v -> AllocM v (Expr v)
lookup v = AllocM $ gets (M.! v)

compileStmt :: Ord v => Stmt v -> AllocM v (Expr v)
compileStmt (Bind v e xs) = do
  xs' <- traverse lookup xs
  let args = foldr1 (\a b -> Prim Fork @@ a @@ b) xs'
  alloc v (AndThen args e)
  lookup v
compileStmt (Run e xs) = do
  xs' <- traverse lookup xs
  let args = foldr1 (\a b -> Prim Fork @@ a @@ b) xs'
  pure $ AndThen args e

desugar :: [Stmt String] -> Expr String
desugar ss =
  let (out, binds) = runWriter $ flip evalStateT (M.singleton "in" "nop") $ unAllocM $ foldr1 (*>) $ fmap compileStmt ss
  in quotient $ foldr AndThen out binds

quotient :: Expr a -> Expr a
quotient = cata \case
  AndThenF (Prim Nop) x -> x
  AndThenF x (Prim Nop) -> x
  x -> embed x

