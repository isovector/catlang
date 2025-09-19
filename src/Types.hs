{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

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
  | Fork (Expr a) (Expr a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance IsString a => IsString (Expr a) where
  fromString s =
    case readMaybe $ mapFirst toUpper s of
      Just p -> Prim p
      Nothing -> Var $ fromString s

data Val
  = VPair Val Val
  | VInl Val
  | VInr Val
  | VLit Lit
  | VFunc (Val -> Val)
  deriving stock Show

instance Show (a -> b) where
  show _ = "<fn>"

instance IsString Val where
  fromString = VLit . fromString


mapFirst :: (Char -> Char) -> String -> String
mapFirst _ [] = []
mapFirst f (c : cs) = f c : cs

data Lit
  = Unit
  | Str String
  | Char Char
  | Num Integer
  deriving stock (Eq, Ord, Show, Data, Typeable)

instance IsString Lit where
  fromString = Str

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
    -- Fork -> S.singleton Cocartesian
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
  , Bind "z" "nop" ["x"]
  , Run "nop" ["y", "x"]
  ]

(@@) :: Expr a -> Expr a -> Expr a
(@@) f a = App f a
infixl 1 @@

desugared :: Expr String
desugared = quotient $ foldr AndThen "nop"
  [ Fork "proj1" "nop"  -- ("x", in)
  , Fork (AndThen "proj2" "proj2") "nop"  -- ("y", ("x", in))
  , Fork "proj1" $ AndThen "proj2" "proj1" -- ("y", "x")
  ]


newtype AllocM v a = AllocM { unAllocM :: StateT (Map v (Expr v)) (Writer [Expr v]) a }
  deriving newtype (Functor, Applicative, Monad)
  deriving (Semigroup, Monoid) via Ap (AllocM v) a

alloc :: Ord v => v -> Expr v -> AllocM v ()
alloc v e = AllocM $ do
  tell $ pure $ Fork e (Prim Nop)
  -- succ everything in the context
  modify $ fmap $ AndThen $ Prim Proj2
  modify $ M.insert v $ Prim Proj1

lookup :: Ord v => v -> AllocM v (Expr v)
lookup v = AllocM $ gets (M.! v)

compileStmt :: Ord v => Stmt v -> AllocM v (Expr v)
compileStmt (Bind v e xs) = do
  xs' <- traverse lookup xs
  let args = foldr1 Fork xs'
  alloc v (AndThen args e)
  lookup v
compileStmt (Run e xs) = do
  xs' <- traverse lookup xs
  let args = foldr1 Fork xs'
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


eval :: Expr a -> Val
eval (Prim Inl) = VFunc VInl
eval (Prim Inr) = VFunc VInr
eval (Prim Proj1) = VFunc $
  \case
    VPair x _ -> x
    _ -> error "projection of a nonpair"
eval (Prim Proj2) = VFunc $
  \case
    VPair _ y -> y
    _ -> error "projection of a nonpair"
eval (Var _) = error "var!"
eval (Lit l) = VLit l
eval (App (eval -> VFunc f) (eval -> a)) = f a
eval App{} = error "bad app"
eval (AndThen (eval -> VFunc f) (eval -> VFunc g)) = VFunc (g . f)
eval AndThen{} = error "bad then"
eval (Fork (eval -> VFunc f) (eval -> VFunc g)) = VFunc $ \a -> VPair (f a) (g a)
eval Fork{} = error "bad fork"
eval (Prim Nop) = VFunc id
eval (Prim Join) = error "no join yet"

mkPair :: [Val] -> Val
mkPair = foldr1 VPair

run :: Val -> Expr a -> Val
run a (eval -> VFunc f) = f a
run _ _ = error "running a nonfunction"

