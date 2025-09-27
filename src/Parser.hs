{-# LANGUAGE OverloadedStrings #-}

module Parser where

import qualified Data.Map as M
import Data.Map (Map)
import Test (Var(V))
import Text.PrettyPrint.HughesPJClass (pPrint)
import Control.Applicative hiding (some, many)
import Types
import Control.Monad
import Text.Megaparsec
import Data.Void
import Data.Text (Text, pack)
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L

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
parseExpr = asum
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

parseArgs :: Parser [Var]
parseArgs = asum
  [ pure <$> parseIdentifier
  , between (symbol "(") (symbol ")") $ sepBy1 parseIdentifier $ symbol ","
  ]

data OneOf a = OLeft a | ORight a
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

buildCase :: Var -> [OneOf (Var, Stmt Var)] -> Parser (Cmd Var)
buildCase n [OLeft xl, ORight yr] = pure $ Case n xl yr
buildCase n [ORight yr, OLeft xl] = pure $ Case n xl yr
buildCase _ err = fail $ show err

parseCmd :: Parser (Cmd Var)
parseCmd = asum
  [ do
      L.indentBlock spi $ do
        symbol "case"
        i <- parseIdentifier
        symbol "of"
        pure $ L.IndentSome Nothing (buildCase i) $ do
          parseStmts (\b s -> fmap (, s) b) $ do
            ctor <- asum
              [ fmap OLeft $ symbol "inl"
              , fmap ORight $ symbol "inr"
              ]
            b <- parseIdentifier
            symbol "->"
            pure $ b <$ ctor
  , parseDo
  ]

parseDo :: Parser (Cmd Var)
parseDo = do
  e <- parseExpr
  symbol "-<"
  args <- parseArgs
  pure $ Do e args

parseStmt1 :: Parser (Stmt Var)
parseStmt1 = do
  mbind <- optional $ try $ parseIdentifier <* symbol "<-"
  cmd <- parseCmd
  pure $ case mbind of
    Just bind -> Bind bind cmd
    Nothing -> Run cmd

parseStmts :: (a -> Stmt Var -> b) -> Parser a -> Parser b
parseStmts f ma = asum
  [ try $ f <$> ma <*> parseStmt1
  , L.indentBlock spi $ do
      a <- ma
      pure $ L.IndentSome Nothing (pure . f a . foldr1 More) parseStmt1
  ]

parseTopBind :: Parser (Var, TopDecl Var)
parseTopBind = L.nonIndented spi $ do
  x <- parseIdentifier
  symbol "="
  y <- parseAnonArrow
  void $ optional spi
  pure (x, y)

parseTopBinds :: Parser (Map Var (TopDecl Var))
parseTopBinds = fmap M.fromList $ many parseTopBind

parseAnonArrow :: Parser (TopDecl Var)
parseAnonArrow =
  parseStmts AnonArrow $ parseIdentifier <* symbol "->"

main :: IO ()
main = putStrLn $
  either errorBundlePretty (show . pPrint) $
    parse parseTopBinds "<internal>" $ pack $ unlines
      [ "foo ="
      , " input -> "
      , "  foo <- "
      , "    case a of"
      , "      inl x -> id -< x"
      , "      inr y ->"
      , "        x <- foo bar baz -< y"
      , "        x <- id -< y"
      , "bar = a -> id -< y"
      ]

