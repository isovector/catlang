{-# LANGUAGE OverloadedStrings #-}

module Test where

import Compile
import Data.Map (Map)
import Data.Map qualified as M
import Data.String
import Eval
import Text.PrettyPrint.HughesPJClass hiding (Str, (<>))
import Typecheck
import Types


newtype Var = V {unVar :: String}
  deriving stock (Eq, Ord, Show, Read)
  deriving newtype (IsString)


instance Pretty Var where
  pPrint = text . unVar


instance Pretty a => Pretty (Map Var a) where
  pPrint m = vcat $ do
    (v, a) <- M.toList m
    pure $
      hang (pPrint v <+> "=") 2 $
        pPrint a


programs :: Map Var (TopDecl Var)
programs =
  M.fromList
    [ ("swap",) $
        AnonArrow "in" $
          foldr1
            More
            [ Bind "x" $ Do "proj1" "in"
            , Bind "y" $ Do "proj2" "in"
            , Bind "z" $ Do "id" "in"
            , Run $ Do "id" $ PPair "y" "x"
            ]
    , ("dup",) $
        AnonArrow "in" $
          foldr1
            More
            [ Bind "x" $ Do "proj1" "in"
            , Run $ Do "id" $ PPair "x" "x"
            ]
    , ("simple_branch",) $
        AnonArrow "in" $
          foldr1
            More
            [ Bind "x" $ Do "proj1" "in"
            , Bind "y" $ Do "proj2" "in"
            , Bind "z" $ Do "inr" "x"
            , Run $
                Case
                  "z"
                  ("a", Run $ Do "id" $ PPair "a" "x")
                  ( "b"
                  , foldr1
                      More
                      [ Bind "z" $ Do "id" "y"
                      , Run $ Do "id" $ PPair "b" "y"
                      ]
                  )
            ]
    , ("branch",) $
        AnonArrow "in" $
          foldr1
            More
            [ Bind "p" $ Do "inl" "in"
            , Bind "out" $
                Case
                  "p"
                  ( "a"
                  , foldr1
                      More
                      [ Run $ Do "swap" $ PPair "a" "a"
                      ]
                  )
                  ("_", Run $ Do "dup" "in")
            , Bind "z" $ Do "proj1" "out"
            , Bind "w" $ Do "proj2" "out"
            , Bind "zw" $ Do "id" $ PPair "w" "z"
            , Run $ Do "id" $ PPair "out" "zw"
            ]
    ]


run :: Var -> Val -> IO ()
run v val = do
  let compiled = compileProg programs
      knotted = fmap (inline (compiled M.!)) compiled
      prog = knotted M.! v

  print $ pPrint prog
  putStrLn ""

  let inferred = either error id $ runTcM $ infer prog
  print $ pPrint $ getSummary inferred
  putStrLn ""
  VFunc f <- pure $ eval prog
  print $ pPrint $ f val


desugared :: Expr Var
desugared =
  quotient $
    foldr
      AndThen
      "id"
      [ Fork "proj1" "id" -- ("x", in)
      , Fork (AndThen "proj2" "proj2") "id" -- ("y", ("x", in))
      , Fork "proj1" $ AndThen "proj2" "proj1" -- ("y", "x")
      ]
