{-# LANGUAGE CPP #-}

module Template where

import Data.Bifunctor (second)
import Data.List (mapAccumL)
import qualified Data.Map.Lazy as M
import Debug.Trace (trace)
import qualified Heap as H
import qualified Lang as L
import qualified Parser as P
import Test (Loc (..), test)
import Prelude hiding (lex)

type Stack = [H.Addr]

type Frames = ()

type Globals = M.Map String H.Addr

data Node
  = NodeApp H.Addr H.Addr
  | NodeFn String [String] (L.Expr String)
  | NodeInt Int
  | NodeIndir H.Addr
  deriving (Eq, Show)

type State = (Stack, Frames, H.Heap Node, Globals)

makeHeap :: [L.Func] -> (H.Heap Node, Globals)
makeHeap = second M.fromList . mapAccumL f H.empty
  where
    f :: H.Heap Node -> L.Func -> (H.Heap Node, (String, H.Addr))
    f h (x, as, e) = (h', (x, a))
      where
        (h', a) = H.alloc h (NodeFn x as e)

compile :: L.Program -> State
compile p = ([(M.!) gs "main"], (), h, gs)
  where
    (h, gs) = makeHeap $ L.prelude ++ p

step :: State -> State
step x@(as'@(a : as), fs, h, gs) =
  case trace (show n) n of
    (NodeInt _) -> undefined
    (NodeApp a' _) -> (a' : as', fs, h, gs)
    (NodeFn _ ns e) -> stepFn x ns e
    (NodeIndir a') -> (a' : as, fs, h, gs)
  where
    n = H.lookup h a
step _ = undefined

stepFn :: State -> [String] -> L.Expr String -> State
stepFn (as, fs, h, gs) ns e = (drop (length ns) as, fs, h', gs)
  where
    h' =
      instantiateUpdate e (as !! length ns) h $
        M.union (M.fromList $ zip ns $ unpackArgs h $ tail as) gs

instantiate :: L.Expr String -> H.Heap Node -> Globals -> (H.Heap Node, H.Addr)
instantiate (L.ExprInt i) h _ = H.alloc h (NodeInt i)
instantiate (L.ExprVar n) h gs = (h, (M.!) gs n)
instantiate (L.ExprApp e0 e1) h0 gs = H.alloc h2 (NodeApp a1 a2)
  where
    (h1, a1) = instantiate e0 h0 gs
    (h2, a2) = instantiate e1 h1 gs
instantiate (L.ExprLet r ds e) h0 gs = instantiate e h1 gs'
  where
    (h1, ds') = mapAccumL f h0 ds
    gs' = M.union (M.fromList ds') gs
    f h0' (n, e') = (h1', (n, a'))
      where
        (h1', a') =
          instantiate e' h0' $
            if r
              then gs'
              else gs
instantiate _ _ _ = undefined

instantiateUpdate ::
  L.Expr String -> H.Addr -> H.Heap Node -> Globals -> H.Heap Node
instantiateUpdate (L.ExprInt i) a h _ = H.update h a $ NodeInt i
instantiateUpdate (L.ExprVar n) a h gs = H.update h a $ NodeIndir $ (M.!) gs n
instantiateUpdate (L.ExprApp e0 e1) a h0 gs = H.update h2 a (NodeApp a1 a2)
  where
    (h1, a1) = instantiate e0 h0 gs
    (h2, a2) = instantiate e1 h1 gs
instantiateUpdate (L.ExprLet r ds e) a h0 gs = instantiateUpdate e a h1 gs'
  where
    (h1, ds') = mapAccumL f h0 ds
    gs' = M.union (M.fromList ds') gs
    f h0' (n, e') = (h1', (n, a'))
      where
        (h1', a') =
          instantiate e' h0' $
            if r
              then gs'
              else gs
instantiateUpdate _ _ _ _ = undefined

unpackArgs :: H.Heap Node -> Stack -> Stack
unpackArgs h = map f
  where
    f a = case H.lookup h a of
      (NodeApp _ a') -> a'
      _ -> undefined

isDone :: State -> Bool
isDone ([a], _, h, _) =
  case H.lookup h a of
    NodeInt _ -> True
    _ -> False
isDone ([], _, _, _) = undefined
isDone _ = False

eval :: State -> [State]
eval x =
  x :
  if isDone x
    then []
    else eval $ step x

#define TEST test (Loc (__FILE__, __LINE__))

tests :: IO ()
tests = do
  TEST (f "main = S K K 3") (NodeInt 3)
  TEST
    ( f $
        unlines
          [ "pair x y f = f x y;",
            "fst p = p K;",
            "snd p = p K1;",
            "f x y =",
            "  letrec",
            "    a = pair x b;",
            "    b = pair y a",
            "  in",
            "  fst (snd (snd (snd a)));",
            "main = f 3 4"
          ]
    )
    (NodeInt 4)
  TEST (f "id x = x; main = twice twice id 3") (NodeInt 3)
  putChar '\n'
  where
    f s = maybe undefined (f' . last . eval . compile) (P.parse s)
      where
        f' ([x], _, h, _) = H.lookup h x
        f' _ = undefined
