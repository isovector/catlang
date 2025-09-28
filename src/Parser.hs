{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Compile
import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text, pack)
import Data.Void
import Test (Var (..))
import Text.Megaparsec
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L
import Text.PrettyPrint.HughesPJClass (pPrint)
import Types


type Parser = Parsec Void Text


sp :: Parser ()
sp = L.space (void " ") (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")


spi :: Parser ()
spi = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")


symbol :: Text -> Parser ()
symbol = void . L.symbol sp


parseIdentifier :: Parser Var
parseIdentifier = fmap V $ L.lexeme sp $ do
  (:) <$> C.letterChar <*> many C.alphaNumChar


parseExpr :: Parser (Expr Var)
parseExpr =
  asum
    [ Proj1 <$ symbol "proj1"
    , Proj2 <$ symbol "proj2"
    , Inl <$ symbol "inl"
    , Inr <$ symbol "inr"
    , Id <$ symbol "id"
    , Dist <$ symbol "dist"
    , Prim Add <$ symbol "(+)"
    , Prim Sub <$ symbol "(-)"
    , Prim Abs <$ symbol "abs"
    , fmap (foldl1 App . fmap Var) $ some parseIdentifier
    ]


data OneOf a = OLeft a | ORight a
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)


buildCase :: Var -> [OneOf (Pat Var, Stmt Var)] -> Parser (Cmd Var)
buildCase n [OLeft xl, ORight yr] = pure $ Case n xl yr
buildCase n [ORight yr, OLeft xl] = pure $ Case n xl yr
buildCase _ err = fail $ show err


parseCmd :: Parser (Cmd Var)
parseCmd =
  asum
    [ do
        L.indentBlock spi $ do
          symbol "case"
          i <- parseIdentifier
          symbol "of"
          pure $ L.IndentSome Nothing (buildCase i) $ do
            parseStmts (\b s -> fmap (,s) b) $ do
              ctor <-
                asum
                  [ fmap OLeft $ symbol "inl"
                  , fmap ORight $ symbol "inr"
                  ]
              b <- parsePat
              symbol "->"
              pure $ b <$ ctor
    , parseDo
    ]


parseDo :: Parser (Cmd Var)
parseDo = do
  e <- parseExpr
  symbol "-<"
  args <- parsePat
  pure $ Do e args


parsePat :: Parser (Pat Var)
parsePat =
  asum
    [ fmap PVar parseIdentifier
    , between (symbol "(") (symbol ")") $ PPair <$> (parsePat <* symbol ",") <*> parsePat
    ]


parseStmt1 :: Parser (Stmt Var)
parseStmt1 =
  asum
    [ do
        symbol "let"
        p <- parsePat
        symbol "="
        args <- parsePat
        pure $ Bind p $ Do Id args
    , do
        mbind <- optional $ try $ parsePat <* symbol "<-"
        cmd <- parseCmd
        pure $ case mbind of
          Just bind -> Bind bind cmd
          Nothing -> Run cmd
    ]


parseStmts :: (a -> Stmt Var -> b) -> Parser a -> Parser b
parseStmts f ma =
  asum
    [ try $ f <$> ma <*> parseStmt1
    , L.indentBlock spi $ do
        a <- ma
        pure $ L.IndentSome Nothing (pure . f a . foldr1 More) parseStmt1
    ]


parseTopBind :: Parser (Var, (Maybe Type, TopDecl Var))
parseTopBind = do
  mtype <- optional $ try $ L.nonIndented spi $ do
    void parseIdentifier
    symbol ":"
    parseType
  L.nonIndented spi $ do
    x <- parseIdentifier
    symbol "="
    y <- parseAnonArrow
    void $ optional spi
    pure (x, (mtype, y))


parseTopBinds :: Parser (Map Var (Maybe Type, TopDecl Var))
parseTopBinds = fmap M.fromList $ many parseTopBind


parseAnonArrow :: Parser (TopDecl Var)
parseAnonArrow =
  parseStmts AnonArrow $ parseIdentifier <* symbol "->"


parseType :: Parser Type
parseType =
  makeExprParser
    ( asum
        [ between (symbol "(") (symbol ")") parseType
        , TyCon IntTy <$ symbol "Int"
        , TyCon StrTy <$ symbol "String"
        , TyCon CharTy <$ symbol "Char"
        , fmap (TyVar . unVar) parseIdentifier
        ]
    )
    [ [InfixN $ Prod <$ symbol "*"]
    , [InfixN $ Coprod <$ symbol "+"]
    , [InfixN $ Arr <$ symbol "->"]
    ]


main :: IO ()
main = do
  f <- readFile "brainfuck.arr"

  putStrLn $
    either errorBundlePretty (show . pPrint . compileAndTypecheckProg) $
      parse parseTopBinds "<internal>" $
        pack f
