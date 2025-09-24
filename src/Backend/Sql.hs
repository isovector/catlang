{-# LANGUAGE OverloadedStrings #-}

module Backend.Sql where

import Control.Arrow ((***))
import Data.Monoid (Endo(..))
import Typecheck
import Text.PrettyPrint.HughesPJClass hiding ((<>), Str)
import Types


data Sql
  = Select [(String, String)] Sql
  | Let Sql Sql
  | LetBound
  | CrossJoin Sql Sql
  | Input
  deriving stock (Eq, Ord, Show)

prettySql :: Sql -> Doc
prettySql (Select fs s) =
  hsep
    [ "SELECT"
    , hsep $ punctuate "," $ do
        (x, y) <- fs
        pure $ text x <+> "AS" <+> text y
    , "FROM"
    , parens $ prettySql s
    ]
prettySql LetBound = "t"
prettySql Input = "input"
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

newtype SqlBuilder = SqlBuilder
  { runSqlBuilder :: Sql -> Sql
  }
  deriving (Semigroup, Monoid) via Endo Sql




sizeCount :: Type -> Int
sizeCount (Prod x y) = sizeCount x + sizeCount y
sizeCount _ = 1

field :: Int -> String
field i = "p" <> show i

move' :: Int -> Int -> Int -> SqlBuilder
move' out_off offset size
  = SqlBuilder
  $ Select
  $ fmap (field *** field)
  $ zip [offset..] [out_off..(out_off + size - 1)]

move :: Int -> Int -> SqlBuilder
move = move' 0


-- example :: Expr ()
-- example = Fork Proj2 Proj1

-- exampleS :: With (Expr ()) Type
-- Right exampleS = runTcM $ infer example


sqlAlg :: Type -> ExprF b SqlBuilder -> SqlBuilder
sqlAlg (Arr (Prod x _) _) Proj1F = move 0 (sizeCount x)
sqlAlg _ Proj1F = error "bad type"
sqlAlg (Arr (Prod x y) _) Proj2F = move (sizeCount x) (sizeCount y)
sqlAlg _ Proj2F = error "bad type"
sqlAlg _ (AndThenF f g) = f <> g
sqlAlg (Arr _ (Prod x y)) (ForkF f g) =
  SqlBuilder $ \input ->
    Let input $ CrossJoin (runSqlBuilder f LetBound) (runSqlBuilder (move' (sizeCount x) 0 (sizeCount y) <> g) LetBound)
sqlAlg _ ForkF{} = error "bad type"

-- --     Proj2F
-- --       | Arr (Prod x y) _ <- ty
-- --       -> pure $ move (sizeCount x) (sizeCount y)
-- --     AndThenF x y ->
-- --       pure $ unlines
-- --         [ "SELECT"
-- --         , y
-- --         , "FROM ("
-- --         , x
-- --         , ")"
-- --         ]
-- --     ForkF x y -> _

