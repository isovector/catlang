{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}

module Typecheck where

import Text.PrettyPrint.HughesPJClass hiding ((<>), Str)
import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.State
import qualified Data.Map as M
import Data.Map (Map)
import Types
import GHC.Generics
import Data.Functor.Foldable
import Data.Functor.Foldable.TH


-- | 'With' is a can of paint over 'Cofree'. It associates an @a@ value at
-- every node in an @f@-shaped tree.
data With f a = With
  { getSummary :: a
  , getContext :: Base f (With f a)
  }
  deriving stock (Generic)



class Show (Base f x) => ShowBase f x
instance Show (Base f x) => ShowBase f x

deriving stock instance (Show x, forall y. Show y => ShowBase f y) => Show (With f x)
deriving stock instance Functor (Base f) => Functor (With f)
deriving stock instance Foldable (Base f) => Foldable (With f)
deriving stock instance Traversable (Base f) => Traversable (With f)


-- | Compute a 'With' by folding the summarized value at each point in the
-- tree.
summarize :: Recursive t => (Base t (With t x) -> x) -> t -> With t x
summarize f = cata $ \b -> With (f b) b


-- | Eliminate a 'With' by forgetting the summarized values.
unsummarize :: Corecursive t => With t x -> t
unsummarize (With _ t) = embed $ fmap unsummarize t


-- | Like 'cata', except that it gives you access to the summarized value at
-- each step.
withCata :: Recursive t => (x -> Base t a -> a) -> With t x -> a
withCata f (With x t) = f x $ fmap (withCata f) t


type Name = String

data Type
  = Prod Type Type
  | Coprod Type Type
  | Arr Type Type
  | TyCon LitTy
  | TyVar Name
  deriving stock (Eq, Ord, Show, Generic)

makeBaseFunctor [''Type]

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

newtype Subst = Subst { unSubst :: Map Name Type  }
  deriving newtype (Eq, Ord, Show)

class CanSubst a where
  subst :: Subst -> a -> a

instance CanSubst Type where
  subst (Subst s) = cata $ \case
    TyVarF a
      | Just t <- M.lookup a s -> t
    x -> embed x

instance CanSubst a => CanSubst (Map k a) where
  subst s = fmap (subst s)

instance Semigroup Subst where
  Subst t1 <> s@(Subst t2) = Subst $ subst s t1 <> t2

instance Monoid Subst where
  mempty = Subst mempty


class CanUnify a where
  mgu :: a -> a -> TcM a

mgu' :: (CanUnify a, CanSubst a) => a -> a -> TcM a
mgu' x y = do
  s <- TcM $ gets tcm_subst
  mgu (subst s x) (subst s y)

instance CanUnify Type where
  mgu (Prod x1 y1) (Prod x2 y2) =
    Prod <$> mgu x1 x2 <*> mgu' y1 y2
  mgu (Coprod x1 y1) (Coprod x2 y2) =
    Coprod <$> mgu x1 x2 <*> mgu' y1 y2
  mgu (Arr x1 y1) (Arr x2 y2) =
    Arr <$> mgu x1 x2 <*> mgu' y1 y2
  mgu (TyVar x) y = varBind x y
  mgu y (TyVar x) = varBind x y
  mgu x y = fail $ unwords
    [ "Cannot unify"
    , show x
    , "with"
    , show y
    ]

varBind :: Name -> Type -> TcM Type
varBind n v =
  TcM $ do
    -- traceM $ unwords
    --   [ "!!!binding:"
    --   , show n
    --   , "to"
    --   , show v
    --   ]
    modify $ \s ->
      s { tcm_subst = mappend (Subst $ M.singleton n v) $ tcm_subst s }
    gets $ (M.! n) . unSubst . tcm_subst

data TcMState = TcMState
  { tcm_subst :: Subst
  , tcm_fresh :: Int
  }
  deriving stock (Eq, Ord, Show)

fresh :: TcM Name
fresh = TcM $ do
  x <- gets tcm_fresh
  modify $ \s -> s { tcm_fresh = tcm_fresh s + 1 }
  pure $ "$" <> show x


newtype TcM a = TcM {unTcM :: ExceptT String (State TcMState) a}
  deriving newtype (Functor, Applicative, Monad)


instance MonadFail TcM where
  fail = TcM . ExceptT . pure . Left


unify :: Type -> Type -> TcM Subst
unify x y = do
  s <- TcM $ gets tcm_subst
  void $ mgu (subst s x) (subst s y)
  TcM $ gets tcm_subst


infer :: Expr a -> TcM (With (Expr a) Type)
infer (AndThen x y) = do
  x'@(With (Arr xin t1) _) <- infer x
  y'@(With (Arr t2 yout) _) <- infer y
  s <- unify t1 t2
  pure $ With (subst s $ Arr xin yout) $ AndThenF x' y'
infer Proj1 = do
  t1 <- fmap TyVar fresh
  t2 <- fmap TyVar fresh
  pure $ With (Arr (Prod t1 t2) t1) Proj1F
infer Proj2 = do
  t1 <- fmap TyVar fresh
  t2 <- fmap TyVar fresh
  pure $ With (Arr (Prod t1 t2) t2) Proj2F
infer Inl = do
  t1 <- fmap TyVar fresh
  t2 <- fmap TyVar fresh
  pure $ With (Arr t1 (Prod t1 t2)) InlF
infer Inr = do
  t1 <- fmap TyVar fresh
  t2 <- fmap TyVar fresh
  pure $ With (Arr t2 (Prod t1 t2)) InrF
infer (Fork x y) = do
  x'@(With (Arr t1 xout) _) <- infer x
  y'@(With (Arr t2 yout) _) <- infer y
  s <- unify t1 t2
  pure $ With (subst s $ Arr t1 (Prod xout yout)) $ ForkF x' y'
infer (Join x y) = do
  x'@(With (Arr xin t1) _) <- infer x
  y'@(With (Arr yin t2) _) <- infer y
  s <- unify t1 t2
  pure $ With (subst s $ Arr (Coprod xin yin) t1) $ JoinF x' y'
infer Id = do
  t1 <- fmap TyVar fresh
  pure $ With (Arr t1 t1) $ IdF
infer Dist = do
  t1 <- fmap TyVar fresh
  t2 <- fmap TyVar fresh
  t3 <- fmap TyVar fresh
  pure $ With (Arr (Prod (Coprod t1 t2) t3) (Coprod (Prod t1 t3) (Prod t2 t3))) DistF
infer (Cochoice f) = do
  t1 <- fmap TyVar fresh
  t2 <- fmap TyVar fresh
  t3 <- fmap TyVar fresh
  f'@(With ty _) <- infer f
  s <- unify ty $ Arr (Coprod t1 t3) (Coprod t2 t3)
  pure $ With (subst s $ Arr t1 t2) $ CochoiceF f'
infer (Costrong f) = do
  t1 <- fmap TyVar fresh
  t2 <- fmap TyVar fresh
  t3 <- fmap TyVar fresh
  f'@(With ty _) <- infer f
  s <- unify ty $ Arr (Prod t1 t3) (Prod t2 t3)
  pure $ With (subst s $ Arr t1 t2) $ CostrongF f'
infer (Lit (Str s)) = pure $ With (TyCon StrTy) $ LitF $ Str s
infer (Lit (Char c)) = pure $ With (TyCon CharTy) $ LitF $ Char c
infer (Lit (Nat n)) = pure $ With (TyCon NatTy) $ LitF $ Nat n
infer App{} = error "can't infer apps"
infer Var{} = error "can't infer var"


subbing :: CanSubst a => a -> TcM a
subbing a = do
  s <- TcM $ gets tcm_subst
  pure $ subst s a


instance (Functor (Base f), CanSubst a) => CanSubst (With f a) where
  subst s = fmap (subst s)


runTcM :: CanSubst a => TcM a -> Either String a
runTcM = flip evalState (TcMState mempty 0) . runExceptT . unTcM . (subbing =<<)
