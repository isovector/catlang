{-# LANGUAGE OverloadedStrings #-}

module Test where

import Compile
import Data.String
import Text.PrettyPrint.HughesPJClass hiding ((<>), Str)
import Types


newtype Var = V { unVar :: String }
  deriving stock (Eq, Ord, Show)
  deriving newtype IsString

instance Pretty Var where
  pPrint = text . unVar


progSwap :: Stmt Var
progSwap = foldr1 More
  [ Bind "x" $ Do "proj1" ["in"]
  , Bind "y" $ Do "proj2" ["in"]
  , Bind "z" $ Do "id" ["in"]
  , Run $ Do "id" ["y", "x"]
  ]


progDup :: Stmt Var
progDup = foldr1 More
  -- NOTE(sandy): need to manually rename so the occurance count works properly
  [ Bind "x_dup" $ Do "proj1" ["in"]
  , Run $ Do "id" ["x_dup", "x_dup"]
  ]


simpleBranch :: Stmt Var
simpleBranch = foldr1 More
  [ Bind "x" $ Do "proj1" ["in"]
  , Bind "y" $ Do "proj2" ["in"]
  , Run $ Case "x"
      ("a", Run $ Do "id" ["a", "x"])
      ("b", foldr1 More
        [ Bind "z" $ Do "id" ["y"]
        , Run $ Do "id" ["b", "y"]
        ])
  ]


progBranch :: Stmt Var
progBranch = foldr1 More
  [ Bind "p" $ Do "inl" ["in"]
  , Bind "out" $ Case "p"
      ("_", progSwap)
      ("_", progDup)
  , Bind "z" $ Do "proj1" ["out"]
  , Bind "w" $ Do "proj2" ["out"]
  , Bind "zw" $ Do "id" ["w", "z"]
  , Run $ Do "id" ["out", "zw"]
  ]


desugared :: Expr Var
desugared = quotient $ foldr AndThen "id"
  [ Fork "proj1" "id"  -- ("x", in)
  , Fork (AndThen "proj2" "proj2") "id"  -- ("y", ("x", in))
  , Fork "proj1" $ AndThen "proj2" "proj1" -- ("y", "x")
  ]

