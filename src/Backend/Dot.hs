{-# LANGUAGE RecursiveDo     #-}
{-# LANGUAGE TemplateHaskell #-}

module Backend.Dot where

import Data.List (intercalate)
import Data.Semigroup
import qualified Data.Map.Monoidal as MM
import Data.Map.Monoidal (MonoidalMap)
import Data.Traversable
import Data.Foldable
import Backend.TH
import Control.Category
import Types
import Control.Arrow
import Control.Monad.State
import Control.Monad.Trans.Writer
import Prelude hiding (id, (.))
import Control.Category.Cartesian
import Control.Category.Monoidal
import Control.Category.Recursive
import Unsafe.Coerce

data Component = Component
  { c_id :: Int
  , c_label :: String
  }
  deriving stock (Eq, Ord, Show)

data Input = Input
  { i_component :: Component
  , i_output :: Int
  }
  deriving stock (Eq, Ord, Show)

data Output = Output
  { o_component :: Component
  , o_output :: Int
  }
  deriving stock (Eq, Ord, Show)


class ToDot a where
  toDot :: a -> String

componentName :: Component -> String
componentName = mappend "c" . show . c_id

instance ToDot Input where
  toDot (Input x y) = componentName x <> ":i" <> show y

instance ToDot Output where
  toDot (Output x y) = componentName x <> ":o" <> show y

portCount :: (Output, Input) -> MonoidalMap Component (Max Int, Max Int)
portCount (Output c1 m, Input c2 n) = mconcat
  [ MM.singleton c1 (mempty, Max m)
  , MM.singleton c2 (Max n, mempty)
  ]

makePorts :: String -> Int -> String
makePorts s n
  | n == minBound = mempty
  | otherwise
  = intercalate "|" $
    fmap (\i ->
      mconcat $
        [ "<"
        , s
        , show i
        , ">"
        ]
      ) [0.. n]

genNodes :: MonoidalMap Component (Max Int, Max Int) -> String
genNodes mm = unlines $ do
  (c, (Max is, Max os)) <- MM.toList mm
  let inputs = makePorts "i" is
      outputs = makePorts "o" os
  pure $ mconcat
    [ componentName c
    , " [label=\""
    , mconcat
        [ inputs
        , "|"
        , c_label c
        , "|"
        , outputs
        ]
    , "\"];"
    ]


data Bus shape val where
  IntBus :: val -> Bus Int val
  StrBus :: val -> Bus String val
  CharBus :: val -> Bus Char val
  PairBus :: Bus a val -> Bus b val -> Bus (a, b) val
  LeftBus :: Bus a val -> Bus (Either a b) val
  RightBus :: Bus b val -> Bus (Either a b) val
  CopairBus :: Bus a val -> Bus b val -> Bus (Either a b) val

deriving stock instance Functor (Bus shape)
deriving stock instance Foldable (Bus shape)
deriving stock instance Traversable (Bus shape)


type BusM = WriterT [(Output, Input)] (State Int)

newtype a +> b = C
  { unC :: Kleisli BusM (Bus a Output) (Bus b Output)
  }

instance Category (+>) where
  id = C $ arr id
  C g . C f = C $ g . f

instance SymmetricProduct (+>) where
  swap = undefined
  reassoc = undefined

instance MonoidalProduct (+>) where
  first' = undefined

instance Cartesian (+>) where
  C (Kleisli f) &&& C (Kleisli g) =
    C $ Kleisli $ \z -> do
      a <- f z
      b <- g z
      pure $ PairBus a b
  consume = undefined
  copy = undefined
  fst' =
    C $ Kleisli $ \case
      PairBus x _ -> pure x
  snd' =
    C $ Kleisli $ \case
      PairBus _ x -> pure x

newComponent :: String -> BusM Component
newComponent s = gets (flip Component s) <* modify (+ 1)


instance IntLits (+>) where
  intLit n = C $ Kleisli $ const $ do
    comp <- newComponent $ show n
    pure $ IntBus $ Output comp 0
  addPrim = C $ Kleisli $ \(PairBus (IntBus x) (IntBus y)) -> do
    comp <- newComponent "+"
    tell
      [ (x, Input comp 0)
      , (y, Input comp 1)
      ]
    pure $ IntBus $ Output comp 0
  subPrim = C $ Kleisli $ \(PairBus (IntBus x) (IntBus y)) -> do
    comp <- newComponent "-"
    tell
      [ (x, Input comp 0)
      , (y, Input comp 1)
      ]
    pure $ IntBus $ Output comp 0
  absPrim = C $ Kleisli $ \(IntBus x) -> do
    comp <- newComponent "abs"
    tell
      [ (x, Input comp 0)
      ]
    pure $ CopairBus (IntBus $ Output comp 0) (IntBus $ Output comp 1)

instance SymmetricSum (+>) where
  swapE = undefined
  reassocE = undefined

instance MonoidalSum (+>) where
  left = undefined
  right = undefined

instance Cocartesian (+>) where
  C (Kleisli f) ||| C (Kleisli g) = C $ Kleisli $ \case
    CopairBus x y -> do
      a <- f x
      b <- g y
      comp <- newComponent "▽"
      tell $ fmap (, Input comp 0) $ toList a
      tell $ fmap (, Input comp 0) $ toList b
      out <- flip evalStateT 0 $ for a $ const $ do
        ix <- get
        modify (+ 1)
        pure $ Output comp ix
      pure out
    LeftBus x -> f x
    RightBus y -> g y

  injectL = C $ Kleisli $ \z -> do
    c <- newComponent "inl"
    tell $ fmap (, Input c 0) $ toList z
    out <- flip evalStateT 0 $ for z $ const $ do
      ix <- get
      modify (+ 1)
      pure $ Output c ix
    pure $ LeftBus out
  injectR = C $ Kleisli $ \z -> do
    c <- newComponent "inr"
    tell $ fmap (, Input c 0) $ toList z
    out <- flip evalStateT 0 $ for z $ const $ do
      ix <- get
      modify (+ 1)
      pure $ Output c ix
    pure $ RightBus out
  unify = undefined
  tag = undefined

instance Distrib (+>) where
  distribute = C $ Kleisli $ \case
    PairBus (CopairBus x y) z -> do
      pure $ CopairBus (PairBus x z) (PairBus y z)
    -- PairBus (LeftBus x) z ->
    --   pure $ LeftBus (PairBus x z)
    -- PairBus (RightBus x) z ->
    --   pure $ RightBus (PairBus x z)


instance ToDot (Int +> c) where
  toDot c = do
    let edges = runBus c

    unlines
      [ "digraph structs {"
      , "node [shape=Mrecord]"
      , genNodes $ foldMap portCount edges
      , unlines $ do
          (o, i) <- edges
          pure $ mconcat
            [ toDot o
            , " -> "
            , toDot i
            , ";"
            ]
      , "}"
      ]
    -- let edges = runBus c
    --  in

unbus :: Bus (Either b s) Output -> (Bus b Output, Bus s Output)
unbus (CopairBus l r) = (l, r)
unbus (LeftBus l) = (l, unsafeCoerce $ IntBus (Component (-1) "loop"))
unbus (RightBus r) = (unsafeCoerce $ IntBus (Component (-1) "loop"), r)

instance Recursive (+>) where
  recurseR = undefined
  recurseL (C (Kleisli f)) = C $ Kleisli $ \a -> mdo
    (unbus -> ~(l, r)) <- f $ CopairBus a r
    pure l

runBus :: Int +> c -> [(Output, Input)]
runBus = flip evalState 1 . execWriterT . ($ mkInputs) . runKleisli . unC

mkInputs :: Bus Int Output
mkInputs = IntBus $ Output (Component 0 "Input") 0


test :: Int +> Int
test = $(toCategory $ Cochoice $
    foldr1
      AndThen
      [ Join Id Id
      , Fork
          ( foldr1
              AndThen
              [ Fork Id (Lit $ Int 10)
              , Prim Sub
              , Prim Abs
              ]
          )
          Id
      , Dist
      , Join
          ( foldr1
              AndThen
              [ Proj2
              , Fork Id (Lit $ Int 1)
              , Prim Add
              , Inr
              ]
          )
          $ AndThen Proj2 Inl
      ]
      )

