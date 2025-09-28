{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}

module Compile where

import Typecheck
import           Control.Monad.Trans.State
import           Control.Monad.Writer
import           Data.Foldable
import           Data.Functor.Foldable
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid
import           Data.Set (Set)
import qualified Data.Set as S
import           Prelude hiding (lookup)
import           Types


data AllocState v = AllocState
  { as_lookup :: Map v (Expr v)
  }


newtype AllocM v a = AllocM { unAllocM :: StateT (AllocState v) (Writer [Expr v]) a }
  deriving newtype (Functor, Applicative, Monad, MonadWriter [Expr v])
  deriving (Semigroup, Monoid) via Ap (AllocM v) a


stackSucc :: AllocM v ()
stackSucc = AllocM $ modify $ \as -> as { as_lookup = fmap (AndThen Proj2) $ as_lookup as }


alloc :: Ord v => v -> Expr v -> AllocM v ()
alloc v e = AllocM $ do
  tell $ pure $ Fork e Id
  unAllocM stackSucc
  modify $ \as -> as { as_lookup = M.insert v Proj1 $ as_lookup as }

inform :: Ord v => v -> Expr v -> AllocM v ()
inform v e = AllocM $ modify $ \as -> as { as_lookup = M.insert v e $ as_lookup as }



lookup :: Ord v => v -> AllocM v (Expr v)
lookup v = AllocM $ gets $ (M.! v) . as_lookup


compileStmt
  :: Ord v
  => Set v
  -- ^ binders which need to be allocated, rather than just inlined
  -> Stmt v -> AllocM v ()
compileStmt allocs (More a b) = compileStmt allocs a >> compileStmt allocs b
compileStmt allocs (Bind p c) = do
  e <- hearMeNow $ compileCmd allocs c
  bindPat allocs p e
compileStmt allocs (Run c) = compileCmd allocs c


bindPat :: Ord v => Set v -> Pat v -> Expr v -> AllocM v ()
bindPat allocs (PVar v) e = do
  case S.member v allocs of
    True -> alloc v e
    False -> inform v e
bindPat allocs (PPair a b) e = do
  bindPat allocs a $ AndThen e Proj1
  bindPat allocs b $ AndThen e Proj2


compileCmd
  :: Ord v
  => Set v
  -- ^ binders which need to be allocated, rather than just inlined
  -> Cmd v -> AllocM v ()
compileCmd allocs (Case a (x, l) (y, r)) = do
  a' <- lookup a
  l' <-
    isolate $ do
      -- optimization opportunity: this is already on the stack, so we don't
      -- actually need to allocate for it.
      bindPat allocs x Proj1
      compileStmt allocs l
  r' <-
    isolate $ do
      -- optimization opportunity: this is already on the stack, so we don't
      -- actually need to allocate for it.
      bindPat allocs y Proj1
      compileStmt allocs r
  tell $ pure $ foldr1 AndThen
    [ Fork a' Id
    , Dist
    , Join l' r'
    ]
compileCmd _ (Do e xs) = do
  xs' <- traverse lookup xs
  let args = buildPat xs'
  tell $ pure $ AndThen args e

buildPat :: Pat (Expr v) -> Expr v
buildPat = cata $ \case
  PVarF p -> p
  PPairF x y -> Fork x y


useCount :: Ord a => Stmt a -> Map a Int
useCount (More a b) = M.unionsWith (+) [useCount a, useCount b]
useCount (Run c) = useCountCmd c
useCount (Bind _ c) = useCountCmd c


useCountCmd :: Ord a => Cmd a -> Map a Int
useCountCmd (Do _ x) = M.fromListWith (+) $ fmap (, 1) $ toList x
-- TODO(sandy): bug in this case; variable with the same name which get
-- introduced in the branches get considered together. renaming will fix it
useCountCmd (Case a (_x, l) (_y, r)) = M.unionsWith (+) [M.singleton a 1, useCount l, useCount r]


desugar :: Ord a => TopDecl a -> Expr a
desugar (AnonArrow input ss) =
  let counts = useCount ss
      needs_alloc = M.keysSet $ M.filter (> 1) counts
      (_, binds)
        = runWriter
        $ flip evalStateT (AllocState $ M.singleton input Id)
        $ unAllocM
        $ compileStmt needs_alloc ss
  in quotient $ foldr AndThen Id binds


compileProg :: (Functor t, Ord a) => t (TopDecl a) -> t (Expr a)
compileProg = fmap desugar

compileAndTypecheckProg
  :: (Traversable t, Ord a)
  => t (Maybe Type, TopDecl a)
  -> Either String (t (Expr a))
compileAndTypecheckProg = traverse $ \(mty, dec) -> do
  let e = desugar dec
  runTcM' $ do
    exp' <- infer e
    for_ mty $ unify $ getSummary exp'
    pure e



quotient :: Expr a -> Expr a
quotient = cata \case
  AndThenF Id x -> x
  AndThenF x Id -> x
  AndThenF (Fork f _) (Proj1 :. k) -> f :. k
  AndThenF (Fork _ g) (Proj2 :. k) -> g :. k
  x -> embed x

hearMeNow :: AllocM v () -> AllocM v (Expr v)
hearMeNow (AllocM x) = AllocM $ do
  (_, binds) <- censor (const mempty) $ listen x
  pure $ foldr AndThen Id binds

-- | Run the action but don't touch the allocation state
isolate :: AllocM v () -> AllocM v (Expr v)
isolate (AllocM x) = AllocM $ do
  s <- get
  (_, binds) <- censor (const mempty) $ listen x
  put s
  pure $ foldr AndThen Id binds
