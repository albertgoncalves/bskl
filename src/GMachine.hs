{-# LANGUAGE CPP #-}

module GMachine where

import Data.List (mapAccumL)
import qualified Data.Map.Lazy as M
import qualified Heap as H
import Lang (Expr (..), Func, Program, prelude)
import Parser (parse)
import Test (Loc (..), test)

data Inst
  = InstUnwind
  | InstPushGlobal String
  | InstPushInt Int
  | InstPush Int
  | InstMkApp
  | InstUpdate Int
  | InstPop Int
  deriving (Eq, Show)

data Node
  = NodeInt Int
  | NodeApp H.Addr H.Addr
  | NodeGlobal Int [Inst]
  | NodeIndir H.Addr
  deriving (Eq, Show)

type Globals = M.Map String H.Addr

type State = ([Inst], [H.Addr], H.Heap Node, Globals)

step :: State -> State
step (i : is, as, h, gs) = dispatch i (is, as, h, gs)
step _ = undefined

dispatch :: Inst -> State -> State
dispatch (InstPushGlobal s) = pushGlobal s
dispatch (InstPushInt n) = pushInt n
dispatch InstMkApp = mkApp
dispatch (InstPush n) = push n
-- dispatch (InstSlide n) = slide n
dispatch InstUnwind = unwind
dispatch (InstUpdate n) = update n
dispatch (InstPop n) = pop n

pushGlobal :: String -> State -> State
pushGlobal s (is, as, h, gs) = (is, (M.!) gs s : as, h, gs)

pushInt :: Int -> State -> State
pushInt n (is, as, h, gs) = (is, a : as, h', gs)
  where
    s = show n
    (h', a) =
      if M.member s gs
        then (h, (M.!) gs s)
        else H.alloc h (NodeInt n)

mkApp :: State -> State
mkApp (is, a0 : a1 : as, h, gs) = (is, a : as, h', gs)
  where
    (h', a) = H.alloc h (NodeApp a0 a1)
mkApp _ = undefined

push :: Int -> State -> State
push n (is, as, h, gs) = (is, as !! n : as, h, gs)

-- slide :: Int -> State -> State
-- slide n (is, a : as, h, gs) = (is, a : drop n as, h, gs)
-- slide _ _ = undefined

update :: Int -> State -> State
update n (is, a : as, h, gs) = (is, as, H.update h (as !! n) (NodeIndir a), gs)
update _ _ = undefined

pop :: Int -> State -> State
pop n (is, as, h, gs) = (is, drop n as, h, gs)

unwind :: State -> State
unwind s@(_, as'@(a : as), h, gs) =
  case H.lookup h a of
    NodeInt _ -> s
    NodeApp a' _ -> ([InstUnwind], a' : as', h, gs)
    NodeGlobal n is -> (is, rearrange n h as', h, gs)
    NodeIndir a' -> ([InstUnwind], a' : as, h, gs)
unwind _ = undefined

rearrange :: Int -> H.Heap Node -> [H.Addr] -> [H.Addr]
rearrange n h as = take n (map (f . H.lookup h) $ tail as) ++ drop n as
  where
    f (NodeApp _ a) = a
    f _ = undefined

eval :: State -> [State]
eval s@([], _, _, _) = [s]
eval s = s : eval (step s)

makeHeap :: [Func] -> (H.Heap Node, Globals)
makeHeap = (M.fromList <$>) . mapAccumL allocFn H.empty . map compileFunc

allocFn ::
  H.Heap Node -> (String, Int, [Inst]) -> (H.Heap Node, (String, H.Addr))
allocFn h (s, n, is) = (h', (s, a))
  where
    (h', a) = H.alloc h (NodeGlobal n is)

compileFunc :: (String, [String], Expr String) -> (String, Int, [Inst])
compileFunc (n, ns, e) =
  (n, length ns, compileUnwind e $ M.fromList $ zip ns [0 :: Int ..])

compileUnwind :: Expr String -> M.Map String Int -> [Inst]
compileUnwind e m = compileExpr e m ++ [InstUpdate n, InstPop n, InstUnwind]
  where
    n = M.size m

compileExpr :: Expr String -> M.Map String Int -> [Inst]
compileExpr (ExprVar s) m =
  if M.member s m
    then [InstPush $ (M.!) m s]
    else [InstPushGlobal s]
compileExpr (ExprInt n) _ = [InstPushInt n]
compileExpr (ExprApp e0 e1) m =
  compileExpr e1 m ++ compileExpr e0 (offset 1 m) ++ [InstMkApp]
compileExpr _ _ = undefined

offset :: Int -> M.Map String Int -> M.Map String Int
offset n = M.fromList . map ((+ n) <$>) . M.assocs

compile :: Program -> State
compile p = ([InstPushGlobal "main", InstUnwind], [], h, gs)
  where
    (h, gs) = makeHeap $ prelude ++ p

#define TEST test (Loc (__FILE__, __LINE__))

tests :: IO ()
tests = do
  TEST (f "id x = I x; main = twice twice id 3") (NodeInt 3)
  TEST (f "main = S K K 3") (NodeInt 3)
  TEST (f "main = twice (I I I) 3") (NodeInt 3)
  TEST (f "loop x = loop x; main = K 3 (loop 1)") (NodeInt 3)
  TEST (f "loop = loop; main = K I loop 1") (NodeInt 1)
  TEST (f "h x y = g x y; g x = f x; f = K I; main = f 1 2") (NodeInt 2)
  putChar '\n'
  where
    f = maybe undefined (f' . last . eval . compile) . parse
      where
        f' (_, [x], h, _) = H.lookup h x
        f' _ = undefined
