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
  | Recursion a
      (Sql' a)
      -- ^ base case
      (Sql' a)
      -- ^ recursive case
  | RecursionBound a
  | CrossJoin (Sql' a) (Sql' a)
  | Union (Sql' a) (Sql' a)
  | RawSelect String String (Sql' a)
  | Input
  | Comment String (Sql' a)
  | AddColumns String (Sql' a)
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


wrap :: Sql' Int -> Doc
wrap s = sep
  [ "SELECT *"
  , "FROM"
  , from s
  , "AS _"
  ]

from :: Sql' Int -> Doc
from a@(LetBound{}) = prettySql a
from a@(RecursionBound{}) = prettySql a
from a = parens $ prettySql a


prettySql :: Sql' Int -> Doc
prettySql (AddColumns s sql) =
  sep
    [ "SELECT"
    , text s
    , ", *"
    , "FROM"
    , from sql
    , "AS _"
    ]
prettySql (Select fs s) =
  sep
    [ "SELECT"
    , hsep $ punctuate "," $ do
        (f, val) <- sortOn fst fs
        pure $ maybe "NULL::integer" text val <+> "AS" <+> text f
    , "FROM"
    , from s
    , "AS _"
    ]
prettySql (RawSelect str "" sql) =
  sep
    [ "SELECT"
    , text str
    , "FROM"
    , from sql
    , "AS _"
    ]
prettySql (RawSelect str wher sql) =
  sep
    [ "SELECT"
    , text str
    , "FROM"
    , from sql
    , "AS _"
    , "WHERE"
    , text wher
    ]
prettySql (Filter [] s) = prettySql s
prettySql (Filter ws s) =
  sep
    [ wrap s
    , "WHERE"
    , sep $ punctuate " AND" $ ws <&> \w -> text w <+> "IS NOT NULL"
    ]
prettySql (LetBound n) = "t" <> pPrint n
prettySql Input = "SELECT 0 as f0, 2 as f1"
prettySql (Let n x y) =
  sep
    [ "WITH" <+> ("t" <> pPrint n) <+> "AS"
    , parens $ wrap x
    , wrap y
    ]
prettySql (CrossJoin x y) =
  sep
    [ wrap x
    , "CROSS JOIN"
    , parens $ prettySql y
    ]
prettySql (Union x y) =
  sep
    [ wrap x
    , "UNION"
    , wrap y
    ]
prettySql (Comment x y) =
  vcat
    [ "--" <+> text x
    , prettySql y
    ]
prettySql (Recursion a base rec) =
  sep
    [ "WITH RECURSIVE recursion AS"
    , parens $
        sep
          [ prettySql base
          , "UNION ALL"
          , prettySql rec
          ]
    , "SELECT * FROM recursion ORDER BY step DESC LIMIT 1"
    ]
prettySql (RecursionBound _) = "recursion"

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


sqlAlg :: Type -> ExprF () (Type, SqlBuilder) -> (Type, SqlBuilder)
sqlAlg ty IdF = (ty,) $ mempty
sqlAlg ty@(Arr (enumerate . toFields -> FPair p1 _) _) Proj1F
  = (ty,) $ toCanonical p1
sqlAlg _ Proj1F = error "bad type"
sqlAlg ty@(Arr (enumerate . toFields -> FPair _ p2) _) Proj2F
  = (ty,) $ toCanonical p2
sqlAlg _ Proj2F = error "bad type"
sqlAlg ty (AndThenF f g) = (ty,) $ snd g <> snd f
sqlAlg ty@(Arr _ (enumerate . toFields -> FPair x y)) (ForkF f g) =
  (ty,) $
  SqlBuilder $ \input ->
    let_ () input $
      CrossJoin
        (runSqlBuilder (fromCanonical x <> snd f) $ LetBound ())
        (runSqlBuilder (fromCanonical y <> snd g) $ LetBound ())
sqlAlg _ ForkF{} = error "bad type"
sqlAlg ty@(Arr _ (enumerate . toFields -> FCopair x y)) InlF =
  (ty,) $
  SqlBuilder $ \sql ->
    Comment "inl" $
    Select (toList $ FCopair (fmap (id &&& Just) x) (fmap (, Nothing) y)) sql
sqlAlg _ InlF = error "bad inl"
sqlAlg ty@(Arr _ (enumerate . toFields -> FCopair x y)) InrF =
  let y0 = enumerate y
   in (ty,) $ SqlBuilder $ \sql ->
        Comment "inr" $
        Select (toList $ FCopair (fmap (, Nothing) x) (zipF y $ fmap Just y0)) sql
sqlAlg _ InrF = error "bad inr"
sqlAlg ty@(Arr (enumerate . toFields -> FCopair x y) _) (JoinF f g) =
  (ty,) $ SqlBuilder $ \sql ->
    let_ () sql $ Comment "join" $
      Union
        (runSqlBuilder (snd f <> toCanonical x) $ Filter (toList x) $ LetBound ())
        (runSqlBuilder (snd g <> toCanonical y) $ Filter (toList y) $ LetBound ())
sqlAlg _ JoinF{} = error "bad join"
sqlAlg ty (PrimF Add) = (ty,) $ SqlBuilder $
  RawSelect "f0 + f1 AS f0" ""
sqlAlg ty (PrimF Sub) = (ty,) $ SqlBuilder $
  RawSelect "f0 - f1 AS f0" ""
sqlAlg ty (PrimF Abs) = (ty,) $ SqlBuilder $
  \sql ->
    let_ () sql $
      Union
        (RawSelect "abs(f0) as f0, NULL::integer as f1" "f0 < 0" $ LetBound ())
        (RawSelect "NULL::integer as f0, f0 as f1" "f0 >= 0" $ LetBound ())
sqlAlg
  ty@(Arr
    (enumerate . toFields -> FPair (FCopair ina inb) inc)
    (enumerate . toFields -> FCopair (FPair outa outc1) (FPair outb outc2))
    ) DistF
  = (ty,) $ SqlBuilder $ \sql ->
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
sqlAlg ty
  (CochoiceF
    (Arr (id &&& (enumerate . toFields) -> (Coprod a x, FCopair ain xin))
         (enumerate . toFields -> FCopair bout xout), f)) =
  (ty,) $ SqlBuilder $ \sql ->
    runSqlBuilder (toCanonical bout) $
      Filter (toList bout) $ runSqlBuilder f $
      Recursion ()
        (AddColumns "clock_timestamp() as step" $ runSqlBuilder (f <> snd (sqlAlg (Arr a (Coprod a x)) InlF)) sql)
        ( AddColumns "clock_timestamp() as step" $ Filter (toList xout) $ runSqlBuilder f $ RecursionBound ()
        )
sqlAlg ty (LitF (Int n)) = (ty,) $ SqlBuilder $ RawSelect (show n <> " as f0") ""
sqlAlg ty x = error $ "!!! MISSING CASE: " <> show (ty, () <$ x)


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
example = Cochoice $
  foldr1 AndThen
    [ Join Id Id
    , Fork (foldr1 AndThen
        [ Fork Id (Lit $ Int 10)
        , Prim Sub
        , Prim Abs
        ]
        ) Id
    , Dist
    , Join (foldr1 AndThen
        [ Proj2
        , Fork Id (Lit $ Int 1)
        , Prim Add
        , Inr
        ]
        ) $ foldr1 AndThen
        [ Proj2
        , Fork Id Id
        , Prim Add
        , Inl
        ]
    ]

main :: IO ()
main = do
  print $ pPrint example
  putStrLn ""
  print $ pPrint $ getSummary exampleS
  let sql = flip mappend ";" $ show $ prettySql $ renameLets $ runSqlBuilder (snd $ withCata sqlAlg exampleS) Input
  -- putStrLn ""
  -- putStrLn sql
  writeFile "/tmp/wat" sql
  -- putStrLn ""
  -- z <- readProcess "sqlite3" [] $ unlines
  --   [ ".headers ON"
  --   , sql
  --   ]
  -- putStrLn z
