{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Backend.Sql where

import Data.List (sortOn)
import Unsafe.Coerce
import System.Process (readProcess)
import Data.Functor
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Foldable
import Control.Monad.State
import Control.Arrow ((&&&))
import Data.Monoid (Endo(..))
import Typecheck
import Text.PrettyPrint.HughesPJClass hiding ((<>), Str)
import Types

type FieldName = String

data Sql' a
  = Select [(FieldName, Maybe FieldName)] (Sql' a)
  | Filter [FieldName] (Sql' a)
  | Let a (Sql' a) (Sql' a)
  | LetBound a
  | CrossJoin (Sql' a) (Sql' a)
  | Union (Sql' a) (Sql' a)
  | RawSelect String (Sql' a)
  | Input
  | Comment String (Sql' a)
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

type Sql = Sql' ()

makeBaseFunctor [''Sql']


data Fields a
  = FPair (Fields a) (Fields a)
  | FCopair (Fields a) (Fields a)
  | Field a
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)


zipF :: Fields a -> Fields b -> Fields (a, b)
zipF (FPair a1 a2) (FPair b1 b2) = FPair (zipF a1 b1) (zipF a2 b2)
zipF (FCopair a1 a2) (FCopair b1 b2) = FCopair (zipF a1 b1) (zipF a2 b2)
zipF (Field a) f = fmap (a,) f
zipF f (Field b) = fmap (, b) f
zipF _ _ = error "tried to zip a pair and copair"

toFields :: Type -> Fields ()
toFields (Prod x y) = FPair (toFields x) (toFields y)
toFields (Coprod x y) = FCopair (toFields x) (toFields y)
toFields _ = Field ()

next :: (Enum a, MonadState a m) => m a
next = get <* modify succ


enumerate :: Traversable f => f a -> f FieldName
enumerate = fmap field . flip evalState 0 . traverse (const next)



prettySql :: Sql' Int -> Doc
prettySql (Select fs s) =
  sep
    [ "SELECT"
    , hsep $ punctuate "," $ do
        (f, val) <- sortOn fst fs
        pure $ maybe "NULL" text val <+> "AS" <+> text f
    , "FROM"
    , parens $ prettySql s
    ]
prettySql (RawSelect str sql) =
  sep
    [ "SELECT"
    , text str
    , "FROM"
    , parens $ prettySql sql
    ]
prettySql (Filter [] s) = prettySql s
prettySql (Filter ws s) =
  sep
    [ "SELECT *"
    , "FROM"
    , parens $ prettySql s
    , "WHERE"
    , sep $ punctuate " AND" $ ws <&> \w -> text w <+> "IS NOT NULL"
    ]
prettySql (LetBound n) = "t" <> pPrint n
prettySql Input = "SELECT 1 as f0, 2 as f1"
prettySql (Let n x y) =
  sep
    [ "WITH" <+> ("t" <> pPrint n) <+> "AS"
    , parens $ prettySql x
    , hang ("SELECT * FROM") 2 $ parens $ prettySql y
    ]
prettySql (CrossJoin x y) =
  sep
    [ hang ("SELECT * FROM") 2 $ parens $ prettySql x
    , "CROSS JOIN"
    , parens $ prettySql y
    ]
prettySql (Union x y) =
  sep
    [ hang ("SELECT * FROM") 2 $ parens $ prettySql x
    , "UNION"
    , hang ("SELECT * FROM") 2 $ parens $ prettySql y
    ]
prettySql (Comment _ y) = prettySql y
  -- vcat
  --   [ "--" <+> text x
  --   , prettySql y
  --   ]

newtype SqlBuilder = SqlBuilder
  { runSqlBuilder :: Sql -> Sql
  }
  deriving (Semigroup, Monoid) via Endo Sql


field :: Int -> FieldName
field i = "f" <> show i


exampleS :: With (Expr ()) Type
Right exampleS = runTcM $ infer example


toCanonical :: Fields FieldName -> SqlBuilder
toCanonical fs = SqlBuilder $ Select $ do
  let l = toList fs
  zip (enumerate l) $ fmap Just l

fromCanonical :: Fields FieldName -> SqlBuilder
fromCanonical fs = SqlBuilder $ Select $ do
  let l = toList fs
  zip l $ fmap Just $ enumerate l


sqlAlg :: Type -> ExprF b SqlBuilder -> SqlBuilder
sqlAlg _ IdF = mempty
sqlAlg (Arr ty _) Proj1F
  | FPair p1 _ <- enumerate $ toFields ty
  = toCanonical p1
sqlAlg _ Proj1F = error "bad type"
sqlAlg (Arr ty _) Proj2F
  | FPair _ p2 <- enumerate $ toFields ty
  = toCanonical p2
sqlAlg _ Proj2F = error "bad type"
sqlAlg _ (AndThenF f g) = g <> f
sqlAlg (Arr _ (enumerate . toFields -> FPair x y)) (ForkF f g) =
  SqlBuilder $ \input ->
    let_ () input $
      CrossJoin
        (runSqlBuilder (fromCanonical x <> f) $ LetBound ())
        (runSqlBuilder (fromCanonical y <> g) $ LetBound ())
sqlAlg _ ForkF{} = error "bad type"
sqlAlg (Arr _ (enumerate . toFields -> FCopair x y)) InlF =
  SqlBuilder $ \sql ->
    Comment "inl" $
    Select (toList $ FCopair (fmap (id &&& Just) x) (fmap (, Nothing) y)) sql
sqlAlg _ InlF = error "bad inl"
sqlAlg (Arr _ (enumerate . toFields -> FCopair x y)) InrF =
  let y0 = enumerate y
   in SqlBuilder $ \sql ->
        Comment "inr" $
        Select (toList $ FCopair (fmap (, Nothing) x) (zipF y $ fmap Just y0)) sql
sqlAlg _ InrF = error "bad inr"
sqlAlg (Arr (enumerate . toFields -> FCopair x y) _) (JoinF f g) =
  SqlBuilder $ \sql ->
    let_ () sql $ Comment "join" $
      Union
        (runSqlBuilder (f <> toCanonical x) $ Filter (toList x) $ LetBound ())
        (runSqlBuilder (g <> toCanonical y) $ Filter (toList y) $ LetBound ())
sqlAlg _ JoinF{} = error "bad join"
sqlAlg _ (PrimF Add) = SqlBuilder $
  RawSelect "f0 + f1 AS f0"
sqlAlg
  (Arr
    (enumerate . toFields -> FPair (FCopair ina inb) inc)
    (enumerate . toFields -> FCopair (FPair outa outc1) (FPair outb outc2))
    ) DistF
  = SqlBuilder $ \sql ->
      let_ () sql $ Comment "dist" $
        Union
          (Select
            ( mconcat
                [ toList $ zipF outa $ fmap Just ina
                , toList $ zipF outc1 $ fmap Just inc
                , toList $ fmap (, Nothing) outb
                , toList $ fmap (, Nothing) outc2
                ]
            )
            $ Filter (toList ina) $ LetBound ())
          (Select
            ( mconcat
                [ toList $ zipF outb $ fmap Just inb
                , toList $ zipF outc2 $ fmap Just inc
                , toList $ fmap (, Nothing) outa
                , toList $ fmap (, Nothing) outc1
                ]
            )
            $ Filter (toList inb) $ LetBound ())
sqlAlg _ DistF{} = error "bad dist"


let_ :: a -> Sql' a -> Sql' a -> Sql' a
let_ a (Let b v e1) e2 = Let b v $ let_ a e1 e2
let_ a e1 e2 = Let a e1 e2


-- | Induce a debruijn ordering on the let-binds of a sql. These are carefully
-- constructed so that variables only ever reference their immediate binder, so
-- we can cheat and implement it as an ana.
renameLets :: Sql' a -> Sql' Int
renameLets =
  ana (uncurry $ \n -> \case
    Let _ x y ->
      LetF (n + 1) (n, x) (n + 1, y)
    LetBound _ -> LetBoundF n
    x -> unsafeCoerce $ fmap (n,) $ project x
    ) . (0, )


example :: Expr ()
example = foldr1 AndThen
  [ Fork (AndThen Proj1 Inl) Proj2
  , Dist
  , Join (Prim Add) Proj1
  ]

main :: IO ()
main = do
  print $ pPrint example
  putStrLn ""
  print $ pPrint $ getSummary exampleS
  let sql = flip mappend ";" $ show $ prettySql $ renameLets $ runSqlBuilder (withCata sqlAlg exampleS) Input
  putStrLn ""
  putStrLn sql
  putStrLn ""
  z <- readProcess "sqlite3" [] $ unlines
    [ ".headers ON"
    , sql
    ]
  putStrLn z
