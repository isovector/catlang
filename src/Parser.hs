{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Test (Var(V))
import Text.PrettyPrint.HughesPJClass (pPrint)
import Control.Applicative hiding (some, many)
import Types
import Control.Monad
import Text.Megaparsec
import Data.Void
import Data.Text (Text, pack, unpack)
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void Text


sp :: Parser ()
sp = L.space (void " ") (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

spi :: Parser ()
spi = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")


symbol :: Text -> Parser ()
symbol = void . L.symbol sp


parseIdentifier :: Parser Text
parseIdentifier = fmap pack $ L.lexeme sp $ do
  (:) <$> C.letterChar <*> many C.alphaNumChar

parseExpr :: Parser (Expr Text)
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
  ]

parseArgs :: Parser [Text]
parseArgs = asum
  [ pure <$> parseIdentifier
  , between (symbol "(") (symbol ")") $ sepBy1 parseIdentifier $ symbol ","
  ]

data OneOf a = OLeft a | ORight a
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

buildCase :: Text -> [OneOf (Text, Stmt Text)] -> Parser (Cmd Text)
buildCase n [OLeft xl, ORight yr] = pure $ Case n xl yr
buildCase n [ORight yr, OLeft xl] = pure $ Case n xl yr
buildCase _ err = fail $ show err

parseCmd :: Parser (Cmd Text)
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

parseDo :: Parser (Cmd Text)
parseDo = do
  e <- parseExpr
  symbol "-<"
  args <- parseArgs
  pure $ Do e args

parseStmt1 :: Parser (Stmt Text)
parseStmt1 = do
  mbind <- optional $ try $ parseIdentifier <* symbol "<-"
  cmd <- parseCmd
  pure $ case mbind of
    Just bind -> Bind bind cmd
    Nothing -> Run cmd

parseStmts :: (a -> Stmt Text -> b) -> Parser a -> Parser b
parseStmts f ma = asum
  [ try $ f <$> ma <*> parseStmt1
  , L.indentBlock spi $ do
      a <- ma
      pure $ L.IndentSome Nothing (pure . f a . foldr1 More) parseStmt1
  ]

parseAnonArrow :: Parser (TopDecl Text)
parseAnonArrow = L.nonIndented spi $
  parseStmts AnonArrow $ parseIdentifier <* symbol "->"

main :: IO ()
main = putStrLn $
  either errorBundlePretty (show . pPrint . fmap (fmap (V . unpack))) $
    parse (some parseAnonArrow) "<internal>" $ pack $ unlines
      -- [ "input -> id -< x"
      [ "input -> "
      , "  foo <- "
      , "    case a of"
      , "      inl x -> id -< x"
      , "      inr y ->"
      , "        x <- id -< y"
      , "        x <- id -< y"
      ]



