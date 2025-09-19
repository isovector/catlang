{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

module Types where

import Data.Foldable
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
import Text.PrettyPrint.HughesPJClass hiding ((<>), Str)

data Prim
  = Inl
  | Inr
  | Proj1
  | Proj2
  | Id
  deriving stock (Eq, Ord, Show, Read, Data, Typeable)

instance Pretty Prim where
  pPrint Inl = "inl"
  pPrint Inr = "inr"
  pPrint Proj1 = "prj₁"
  pPrint Proj2 = "prj₂"
  pPrint Id = "id"

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
  pPrintPrec l p (Var a) = pPrintPrec l p a
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
      pPrintPrec l 3 f <+> "▵" <+> pPrintPrec l 3 g
  pPrintPrec l p (Join f g) =
    maybeParens (p >= 5) $
      pPrintPrec l 4 f <+> "▿" <+> pPrintPrec l 4 g

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

instance Pretty Val where
  pPrint (VPair x y) = prettyTuple [x, y]
  -- TODO(sandy): stupid, should do assoc
  pPrint (VInl x) = parens $ "inl" <+> pPrint x
  pPrint (VInr x) = parens $ "inr" <+> pPrint x
  pPrint (VLit x) = pPrint x
  pPrint (VFunc _) = "<fn>"

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

instance Pretty Lit where
  pPrint Unit = "!"
  pPrint (Str s) = pPrint s
  pPrint (Char c) = pPrint c
  pPrint (Num i) = pPrint i

instance IsString Lit where
  fromString = Str

data Stmt a
  = Run (Expr a) [a]
  | Bind a (Expr a) [a]
  | Case a (Stmt a) (Stmt a)
  | More (Stmt a) (Stmt a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

prettyTuple :: Pretty a => [a] -> Doc
prettyTuple [x] = pPrint x
prettyTuple xs = parens $ hsep $ punctuate "," $ fmap pPrint xs

instance Pretty a => Pretty (Stmt a) where
  pPrint (Run e as) =
    pPrint e <+> "-<" <+> prettyTuple as
  pPrint (Bind a e as) =
    pPrint a <+> "<-" <+> pPrint e <+> "-<" <+> prettyTuple as
  pPrint (More a b) = pPrint a $$ pPrint b
  pPrint (Case a l r) =
    hang ("case" <+> pPrint a <+> "of") 2 $ vcat
      [ hang "inl ->" 2 $ pPrint l
      , hang "inr ->" 2 $ pPrint r
      ]


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
    Proj1 -> S.singleton Cartesian
    Proj2 -> S.singleton Cartesian
    Id -> mempty
  `extQ` \case
    Unit -> S.singleton Terminal
    Str{} -> S.singleton LitStr
    Char{} -> S.singleton LitChar
    Num{} -> S.singleton LitNum


progSwap :: Stmt String
progSwap = foldr1 More
  [ Bind "x" "proj1" ["in"]
  , Bind "y" "proj2" ["in"]
  , Bind "z" "id" ["in"]
  , Run "id" ["y", "x"]
  ]

progDup :: Stmt String
progDup = foldr1 More
  -- NOTE(sandy): need to manually rename so the occurance count works properly
  [ Bind "x_dup" "proj1" ["in"]
  , Run "id" ["x_dup", "x_dup"]
  ]

progBranch :: Stmt String
progBranch = foldr1 More
  [ Bind "p" "inr" ["in"]
  , Case "p"
      progSwap
      progDup
  ]

(@@) :: Expr a -> Expr a -> Expr a
(@@) f a = App f a
infixl 1 @@

desugared :: Expr String
desugared = quotient $ foldr AndThen "id"
  [ Fork "proj1" "id"  -- ("x", in)
  , Fork (AndThen "proj2" "proj2") "id"  -- ("y", ("x", in))
  , Fork "proj1" $ AndThen "proj2" "proj1" -- ("y", "x")
  ]


newtype AllocM v a = AllocM { unAllocM :: StateT (Map v (Expr v)) (Writer [Expr v]) a }
  deriving newtype (Functor, Applicative, Monad)
  deriving (Semigroup, Monoid) via Ap (AllocM v) a

alloc :: Ord v => v -> Expr v -> AllocM v ()
alloc v e = AllocM $ do
  tell $ pure $ Fork e (Prim Id)
  -- succ everything in the context
  modify $ fmap $ AndThen $ Prim Proj2
  modify $ M.insert v $ Prim Proj1

lookup :: Ord v => v -> AllocM v (Expr v)
lookup v = AllocM $ gets (M.! v)

compileStmt
  :: Ord v
  => Set v
  -- ^ binders which need to be allocated, rather than just inlined
  -> Stmt v -> AllocM v (Expr v)
compileStmt allocs (More a b) = compileStmt allocs a >> compileStmt allocs b
compileStmt allocs (Case a l r) = do
  a' <- lookup a
  l' <- isolate $ compileStmt allocs l
  r' <- isolate $ compileStmt allocs r
  pure $ AndThen a' $ Join l' r'
compileStmt allocs (Bind v e xs) = do
  xs' <- traverse lookup xs
  let args = foldr1 Fork xs'
  let e' = AndThen args e
  case S.member v allocs of
    True -> do
      alloc v e'
    False -> do
      AllocM $ modify $ M.insert v e'
  lookup v
compileStmt _ (Run e xs) = do
  xs' <- traverse lookup xs
  let args = foldr1 Fork xs'
  pure $ AndThen args e

useCount :: Ord a => Stmt a -> Map a Int
useCount (Bind _ _ x) = M.fromListWith (+) $ fmap (, 1) x
useCount (Run _ x) = M.fromListWith (+) $ fmap (, 1) x
useCount (More a b) = M.unionsWith (+) [useCount a, useCount b]
-- TODO(sandy): bug in this case; variable with the same name which get
-- introduced in the branches get considered together. renaming will fix it
useCount (Case a l r) = M.unionsWith (+) [M.singleton a 1, useCount l, useCount r]

desugar :: Stmt String -> Expr String
desugar ss =
  let counts = useCount ss
      needs_alloc = M.keysSet $ M.filter (> 1) counts
      (out, binds)
        = runWriter
        $ flip evalStateT (M.singleton "in" "id")
        $ unAllocM
        $ compileStmt needs_alloc ss
  in quotient $ foldr AndThen out binds

quotient :: Expr a -> Expr a
quotient = cata \case
  AndThenF (Prim Id) x -> x
  AndThenF x (Prim Id) -> x
  AndThenF (Fork f _) (Prim Proj1 :. k) -> f :. k
  AndThenF (Fork _ g) (Prim Proj2 :. k) -> g :. k
  x -> embed x

pattern (:.) :: Expr a -> Expr a -> Expr a
pattern (:.)f g <- (split -> (f, g))
  where
    (:.) f (Prim Id) = f
    (:.) (Prim Id) f = f
    (:.) f g = AndThen f g

split :: Expr a -> (Expr a, Expr a)
split (AndThen (AndThen f g) h) = fmap (flip AndThen $ AndThen g h) $ split f
split (AndThen f g) = (f, g)
split x = (x, Prim Id)


-- | Run the action but don't touch the allocation state
isolate :: AllocM v a -> AllocM v a
isolate (AllocM x) = AllocM $ do
  s <- get
  a <- censor (const mempty) x
  put s
  pure a

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
eval (Join (eval -> VFunc f) (eval -> VFunc g)) =
  VFunc $ \case
    VInl a -> f a
    VInr a -> g a
    _ -> error "join of a nonsum"
eval Join{} = error "bad join"
eval (Prim Id) = VFunc id

mkPair :: [Val] -> Val
mkPair = foldr1 VPair

run :: Val -> Expr a -> IO ()
run a (eval -> VFunc f) = print $ pPrint $ f a
run _ _ = error "running a nonfunction"

