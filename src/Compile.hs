{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}

module Compile where

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


newtype AllocM v a = AllocM { unAllocM :: StateT (Map v (Expr v)) (Writer [Expr v]) a }
  deriving newtype (Functor, Applicative, Monad)
  deriving (Semigroup, Monoid) via Ap (AllocM v) a


stackSucc :: AllocM v ()
stackSucc = AllocM $ modify $ fmap $ AndThen Proj2


alloc :: Ord v => v -> Expr v -> AllocM v ()
alloc v e = AllocM $ do
  tell $ pure $ Fork e Id
  unAllocM stackSucc
  modify $ M.insert v Proj1

inform :: Ord v => v -> Expr v -> AllocM v ()
inform v e = AllocM $ modify $ M.insert v e



lookup :: Ord v => v -> AllocM v (Expr v)
lookup v = AllocM $ gets (M.! v)


compileStmt
  :: Ord v
  => Set v
  -- ^ binders which need to be allocated, rather than just inlined
  -> Stmt v -> AllocM v (Expr v)
compileStmt allocs (More a b) = compileStmt allocs a >> compileStmt allocs b
compileStmt allocs (Bind v c) = do
  e <- compileCmd allocs c
  case S.member v allocs of
    True -> alloc v e
    False -> inform v e
  lookup v
compileStmt allocs (Run c) = compileCmd allocs c


compileCmd
  :: Ord v
  => Set v
  -- ^ binders which need to be allocated, rather than just inlined
  -> Cmd v -> AllocM v (Expr v)
compileCmd allocs (Case a (x, l) (y, r)) = do
  a' <- lookup a
  l' <-
    isolate $ do
      stackSucc
      inform x Proj1
      compileStmt allocs l
  r' <-
    isolate $ do
      stackSucc
      inform y Proj1
      compileStmt allocs r
  pure $ foldr1 AndThen
    [ Fork a' Id
    , Dist
    , Join l' r'
    ]
compileCmd _ (Do e xs) = do
  xs' <- traverse lookup xs
  let args = foldr1 Fork xs'
  pure $ AndThen args e


useCount :: Ord a => Stmt a -> Map a Int
useCount (More a b) = M.unionsWith (+) [useCount a, useCount b]
useCount (Run c) = useCountCmd c
useCount (Bind _ c) = useCountCmd c


useCountCmd :: Ord a => Cmd a -> Map a Int
useCountCmd (Do _ x) = M.fromListWith (+) $ fmap (, 1) x
-- TODO(sandy): bug in this case; variable with the same name which get
-- introduced in the branches get considered together. renaming will fix it
useCountCmd (Case a (_x, l) (_y, r)) = M.unionsWith (+) [M.singleton a 1, useCount l, useCount r]


desugar :: Ord a => TopDecl a -> Expr a
desugar (AnonArrow input ss) =
  let counts = useCount ss
      needs_alloc = M.keysSet $ M.filter (> 1) counts
      (out, binds)
        = runWriter
        $ flip evalStateT (M.singleton input Id)
        $ unAllocM
        $ compileStmt needs_alloc ss
  in quotient $ foldr AndThen out binds


compileProg :: (Functor t, Ord a) => t (TopDecl a) -> t (Expr a)
compileProg = fmap desugar


quotient :: Expr a -> Expr a
quotient = cata \case
  AndThenF Id x -> x
  AndThenF x Id -> x
  AndThenF (Fork f _) (Proj1 :. k) -> f :. k
  AndThenF (Fork _ g) (Proj2 :. k) -> g :. k
  x -> embed x


-- | Run the action but don't touch the allocation state
isolate :: AllocM v (Expr v) -> AllocM v (Expr v)
isolate (AllocM x) = AllocM $ do
  s <- get
  (a, binds) <- censor (const mempty) $ listen x
  put s
  pure $ foldr AndThen a binds
