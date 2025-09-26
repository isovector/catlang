{-# LANGUAGE OverloadedStrings #-}

module Backend.Sql where

import System.Process (readProcess)
import Data.Functor
import Data.Foldable
import Control.Monad.State
import Control.Arrow ((***), (&&&))
import Data.Monoid (Endo(..))
import Typecheck
import Text.PrettyPrint.HughesPJClass hiding ((<>), Str)
import Types

type FieldName = String

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


data Sql
  = Select [(FieldName, Maybe FieldName)] Sql
  | Filter [FieldName] Sql
  | Let Sql Sql
  | LetBound
  | CrossJoin Sql Sql
  | Union Sql Sql
  | Input
  deriving stock (Eq, Ord, Show)

prettySql :: Sql -> Doc
prettySql (Select fs s) =
  hsep
    [ "SELECT"
    , hsep $ punctuate "," $ do
        (field, val) <- fs
        pure $ maybe "NULL" text val <+> "AS" <+> text field
    , "FROM"
    , parens $ prettySql s
    ]
prettySql (Filter [] s) = prettySql s
prettySql (Filter ws s) =
  hsep
    [ "SELECT *"
    , "FROM"
    , parens $ prettySql s
    , "WHERE"
    , hsep $ punctuate " AND" $ ws <&> \w -> text w <+> "IS NOT NULL"
    ]
prettySql LetBound = "t"
prettySql Input = "SELECT 1 as f0"
prettySql (Let x y) =
  vcat
    [ "WITH" <+> "t" <+> "AS"
    , parens $ prettySql x
    , prettySql y
    ]
prettySql (CrossJoin x y) =
  vcat
    [ "SELECT * FROM"
    , parens $ prettySql x
    , "CROSS JOIN"
    , parens $ prettySql y
    ]
prettySql (Union x y) =
  vcat
    [ prettySql x
    , "UNION"
    , prettySql y
    ]

newtype SqlBuilder = SqlBuilder
  { runSqlBuilder :: Sql -> Sql
  }
  deriving (Semigroup, Monoid) via Endo Sql


field :: Int -> FieldName
field i = "f" <> show i


example :: Expr ()
example = AndThen Inr (Join Inr Inl)

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
    Let input $
      CrossJoin
        (runSqlBuilder (fromCanonical x <> f) LetBound)
        (runSqlBuilder (fromCanonical y <> g) LetBound)
sqlAlg _ ForkF{} = error "bad type"
sqlAlg (Arr _ (enumerate . toFields -> FCopair x y)) InlF =
  SqlBuilder $ Select $ toList $ FCopair (fmap (id &&& Just) x) (fmap (, Nothing) y)
sqlAlg _ InlF = error "bad inl"
sqlAlg (Arr _ (enumerate . toFields -> FCopair x y)) InrF =
  let y0 = enumerate y
   in SqlBuilder $ Select $ toList $ FCopair (fmap (, Nothing) x) (zipF y $ fmap Just y0)
sqlAlg _ InrF = error "bad inr"
sqlAlg (Arr (enumerate . toFields -> FCopair x y) _) (JoinF f g) =
  SqlBuilder $ \sql ->
    Let sql $
      Union
        (runSqlBuilder (f <> toCanonical x) $ Filter (toList x) LetBound)
        (runSqlBuilder (g <> toCanonical y) $ Filter (toList y) LetBound)
sqlAlg _ JoinF{} = error "bad join"


main :: IO String
main = readProcess "sqlite3" [] $ flip mappend ";" $ show $ prettySql $ runSqlBuilder (withCata sqlAlg exampleS) Input

