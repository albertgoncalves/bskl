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
  | InstAlloc Int
  | InstSlide Int
  | InstEval
  | InstAdd
  | InstSub
  | InstMul
  | InstDiv
  | InstNeg
  | InstEq
  | InstNe
  | InstLt
  | InstLe
  | InstGt
  | InstGe
  | InstCond [Inst] [Inst]
  deriving (Eq, Show)

data Node
  = NodeInt Int
  | NodeApp H.Addr H.Addr
  | NodeGlobal Int [Inst]
  | NodeIndir H.Addr
  deriving (Eq, Show)

type Frame = ([Inst], [H.Addr])

type Globals = M.Map String H.Addr

type State = ([Inst], [H.Addr], [Frame], H.Heap Node, Globals)

infix 9 .:

(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(f .: g) x y = f $ g x y

step :: State -> State
step (i : is, as, fs, h, gs) = dispatch i (is, as, fs, h, gs)
step _ = undefined

dispatch :: Inst -> State -> State
dispatch (InstPushGlobal s) = pushGlobal s
dispatch (InstPushInt n) = pushInt n
dispatch InstMkApp = mkApp
dispatch (InstPush n) = push n
dispatch InstUnwind = unwind
dispatch (InstUpdate n) = update n
dispatch (InstPop n) = pop n
dispatch (InstAlloc n) = alloc n
dispatch (InstSlide n) = slide n
dispatch InstAdd = binOp (+)
dispatch InstSub = binOp (-)
dispatch InstMul = binOp (*)
dispatch InstDiv = binOp div
dispatch InstNeg = neg
dispatch InstEq = binOp (toInt .: (==))
dispatch InstNe = binOp (toInt .: (/=))
dispatch InstLt = binOp (toInt .: (<))
dispatch InstLe = binOp (toInt .: (<=))
dispatch InstGt = binOp (toInt .: (>))
dispatch InstGe = binOp (toInt .: (>=))
dispatch (InstCond i0 i1) = cond i0 i1
dispatch InstEval = eval'

toInt :: Bool -> Int
toInt True = 1
toInt False = 0

pushGlobal :: String -> State -> State
pushGlobal s (is, as, fs, h, gs) = (is, (M.!) gs s : as, fs, h, gs)

pushInt :: Int -> State -> State
pushInt n (is, as, fs, h, gs) = (is, a : as, fs, h', gs)
  where
    s = show n
    (h', a) =
      if M.member s gs
        then (h, (M.!) gs s)
        else H.alloc h (NodeInt n)

mkApp :: State -> State
mkApp (is, a0 : a1 : as, fs, h, gs) = (is, a : as, fs, h', gs)
  where
    (h', a) = H.alloc h (NodeApp a0 a1)
mkApp _ = undefined

push :: Int -> State -> State
push n (is, as, fs, h, gs) = (is, as !! n : as, fs, h, gs)

slide :: Int -> State -> State
slide n (is, a : as, fs, h, gs) = (is, a : drop n as, fs, h, gs)
slide _ _ = undefined

alloc :: Int -> State -> State
alloc n (is, as, fs, h, gs) = (is, as', fs, h', gs)
  where
    (h', as') = foldr f (h, as) $ replicate n $ NodeIndir H.null
    f x (h'', as'') = (: as'') <$> H.alloc h'' x

update :: Int -> State -> State
update n (is, a : as, fs, h, gs) =
  (is, as, fs, H.update h (as !! n) (NodeIndir a), gs)
update _ _ = undefined

pop :: Int -> State -> State
pop n (is, as, fs, h, gs) = (is, drop n as, fs, h, gs)

unwind :: State -> State
unwind (_, as'@(a : as), fs'@((is'', as'') : fs), h, gs) =
  case H.lookup h a of
    NodeInt _ -> (is'', a : as'', fs, h, gs)
    NodeApp a' _ -> ([InstUnwind], a' : as', fs', h, gs)
    NodeGlobal n is' ->
      if m < n
        then (is'', (as' !! m) : as'', fs, h, gs)
        else (is', rearrange n h as', fs', h, gs)
      where
        m = length as' - 1
    NodeIndir a' -> ([InstUnwind], a' : as, fs', h, gs)
unwind _ = undefined

binOp :: (Int -> Int -> Int) -> State -> State
binOp f (is, a0 : a1 : as, fs, h, gs) =
  case (H.lookup h a0, H.lookup h a1) of
    (NodeInt l, NodeInt r) -> (is, a : as, fs, h', gs)
      where
        (h', a) = H.alloc h (NodeInt $ l `f` r)
    _ -> undefined
binOp _ _ = undefined

neg :: State -> State
neg (is, a : as, fs, h, gs) =
  case H.lookup h a of
    (NodeInt n) -> (is, a' : as, fs, h', gs)
      where
        (h', a') = H.alloc h (NodeInt $ negate n)
    _ -> undefined
neg _ = undefined

cond :: [Inst] -> [Inst] -> State -> State
cond i0 i1 (is, a : as, fs, h, gs) =
  case H.lookup h a of
    (NodeInt 1) -> (i0 ++ is, as, fs, h, gs)
    (NodeInt 0) -> (i1 ++ is, as, fs, h, gs)
    _ -> undefined
cond _ _ _ = undefined

eval' :: State -> State
eval' (is, a : as, fs, h, gs) = ([InstUnwind], [a], (is, as) : fs, h, gs)
eval' _ = undefined

rearrange :: Int -> H.Heap Node -> [H.Addr] -> [H.Addr]
rearrange n h as = take n (map (f . H.lookup h) $ tail as) ++ drop n as
  where
    f (NodeApp _ a) = a
    f _ = undefined

eval :: State -> [State]
eval s@([], _, _, _, _) = [s]
eval s = s : eval (step s)

makeHeap :: [(String, Int, [Inst])] -> (H.Heap Node, M.Map String H.Addr)
makeHeap = (M.fromList <$>) . mapAccumL allocFn H.empty

allocFn ::
  H.Heap Node -> (String, Int, [Inst]) -> (H.Heap Node, (String, H.Addr))
allocFn h (s, n, is) = (h', (s, a))
  where
    (h', a) = H.alloc h (NodeGlobal n is)

-- NOTE: `SC`
compileFunc :: Func -> (String, Int, [Inst])
compileFunc (n, ns, e) =
  (n, length ns, compileUnwind e $ M.fromList $ zip ns [0 :: Int ..])

-- NOTE: `R`
compileUnwind :: Expr String -> M.Map String Int -> [Inst]
compileUnwind e m =
  compileStrictExpr e m ++ [InstUpdate n, InstPop n, InstUnwind]
  where
    n = M.size m

-- NOTE: `C`
compileLazyExpr :: Expr String -> M.Map String Int -> [Inst]
compileLazyExpr (ExprVar s) m =
  if M.member s m
    then [InstPush $ (M.!) m s]
    else [InstPushGlobal s]
compileLazyExpr (ExprInt n) _ = [InstPushInt n]
compileLazyExpr (ExprApp e0 e1) m =
  compileLazyExpr e1 m ++ compileLazyExpr e0 (offset 1 m) ++ [InstMkApp]
compileLazyExpr (ExprLet r ds e) m =
  (if r then compileLetRec else compileLet) compileLazyExpr ds e m
compileLazyExpr _ _ = undefined

-- NOTE: `E`
compileStrictExpr :: Expr String -> M.Map String Int -> [Inst]
compileStrictExpr (ExprInt n) _ = [InstPushInt n]
compileStrictExpr (ExprLet r ds e) m =
  (if r then compileLetRec else compileLet) compileStrictExpr ds e m
compileStrictExpr (ExprApp (ExprApp (ExprVar op) e0) e1) m
  | op == "+" = is ++ [InstAdd]
  | op == "-" = is ++ [InstSub]
  | op == "*" = is ++ [InstMul]
  | op == "/" = is ++ [InstDiv]
  | op == "==" = is ++ [InstEq]
  | op == "/=" = is ++ [InstNe]
  | op == "<" = is ++ [InstLt]
  | op == "<=" = is ++ [InstLe]
  | op == ">" = is ++ [InstGt]
  | op == ">=" = is ++ [InstGe]
  where
    is = compileStrictExpr e1 m ++ compileStrictExpr e0 (offset 1 m)
compileStrictExpr (ExprApp (ExprVar "negate") e) m =
  compileStrictExpr e m ++ [InstNeg]
compileStrictExpr (ExprApp (ExprApp (ExprApp (ExprVar "if") e0) e1) e2) m =
  compileStrictExpr e0 m
    ++ [InstCond (compileStrictExpr e1 m) (compileStrictExpr e2 m)]
compileStrictExpr e m = compileLazyExpr e m ++ [InstEval]

compileLetRec ::
  (Expr String -> M.Map String Int -> [Inst]) ->
  [(String, Expr String)] ->
  (Expr String -> M.Map String Int -> [Inst])
compileLetRec c ds e m =
  [InstAlloc n]
    ++ f ds (n - 1)
    ++ c e (compileArgs ds m)
    ++ [InstSlide $ length ds]
  where
    m' = compileArgs ds m
    n = length ds
    f :: [(String, Expr String)] -> Int -> [Inst]
    f [] (-1) = []
    f ((_, e') : ds') n' =
      compileLazyExpr e' m' ++ [InstUpdate n'] ++ f ds' (n' - 1)
    f _ _ = undefined

compileLet ::
  (Expr String -> M.Map String Int -> [Inst]) ->
  [(String, Expr String)] ->
  (Expr String -> M.Map String Int -> [Inst])
compileLet c ds e m =
  f ds m ++ c e (compileArgs ds m) ++ [InstSlide $ length ds]
  where
    f :: [(String, Expr String)] -> M.Map String Int -> [Inst]
    f [] _ = []
    f ((_, e') : ds') m' = compileLazyExpr e' m' ++ f ds' (offset 1 m')

compileArgs :: [(String, Expr String)] -> M.Map String Int -> M.Map String Int
compileArgs ds m =
  M.union (M.fromList $ zip (map fst ds) [n - 1, n - 2 ..]) (offset n m)
  where
    n = length ds

offset :: Int -> M.Map String Int -> M.Map String Int
offset n = M.fromList . map ((+ n) <$>) . M.assocs

builtIns :: [(String, Int, [Inst])]
builtIns =
  [ ( "+",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstAdd,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( "-",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstSub,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( "*",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstMul,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( "/",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstDiv,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( "negate",
      1,
      [ InstPush 0,
        InstEval,
        InstNeg,
        InstUpdate 1,
        InstPop 1,
        InstUnwind
      ]
    ),
    ( "==",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstEq,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( "~=",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstNe,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( "<",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstLt,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( "<=",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstLe,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( ">",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstGt,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( ">=",
      2,
      [ InstPush 1,
        InstEval,
        InstPush 1,
        InstEval,
        InstGe,
        InstUpdate 2,
        InstPop 2,
        InstUnwind
      ]
    ),
    ( "if",
      3,
      [ InstPush 0,
        InstEval,
        InstCond [InstPush 1] [InstPush 2],
        InstUpdate 3,
        InstPop 3,
        InstUnwind
      ]
    )
  ]

compile :: Program -> State
compile p = ([InstPushGlobal "main", InstEval], [], [], h, gs)
  where
    (h, gs) = makeHeap $ map compileFunc (prelude ++ p) ++ builtIns

#define TEST test (Loc (__FILE__, __LINE__))

testCompile :: IO ()
testCompile = do
  TEST
    (f "Y f = letrec x = f x in x")
    ( Just
        [ ( "Y",
            1,
            [ InstAlloc 1,
              InstPush 0,
              InstPush 2,
              InstMkApp,
              InstUpdate 0,
              InstPush 0,
              InstEval,
              InstSlide 1,
              InstUpdate 1,
              InstPop 1,
              InstUnwind
            ]
          )
        ]
    )
  TEST
    (f "f = 3 + 4 * 5")
    ( Just
        [ ( "f",
            0,
            [ InstPushInt 5,
              InstPushInt 4,
              InstMul,
              InstPushInt 3,
              InstAdd,
              InstUpdate 0,
              InstPop 0,
              InstUnwind
            ]
          )
        ]
    )
  putChar '\n'
  where
    f = ((compileFunc <$>) <$>) . parse

testEval :: IO ()
testEval = do
  TEST (f "id x = I x; main = twice twice id 3") (NodeInt 3)
  TEST (f "main = S K K 3") (NodeInt 3)
  TEST (f "main = twice (I I I) 3") (NodeInt 3)
  TEST (f "loop x = loop x; main = K 3 (loop 1)") (NodeInt 3)
  TEST (f "loop = loop; main = K I loop 1") (NodeInt 1)
  TEST (f "h x y = g x y; g x = f x; f = K I; main = f 1 2") (NodeInt 2)
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
  TEST (f "main = let id1 = I I I in id1 id1 3") (NodeInt 3)
  TEST
    ( f $
        unlines
          [ "cons a b cc n = cc a b;",
            "nil cc cn = cn;",
            "hd list = list K abort;",
            "tl list = list K1 abort;",
            "abort = abort;",
            "infinite x = letrec xs = cons x xs in xs;",
            "main = hd (tl (tl (infinite 4)))"
          ]
    )
    (NodeInt 4)
  TEST (f "main = 3 + 4 * 5") (NodeInt 23)
  TEST (f "main = (20 / 6) * 4") (NodeInt 12)
  TEST (f "loop = loop; main = if (0 == 0) 2 loop") (NodeInt 2)
  TEST (f "loop = loop; main = if (0 ~= 0) loop 3") (NodeInt 3)
  TEST (f "loop = loop; main = if (negate 1 < 1) 2 loop") (NodeInt 2)
  TEST (f "loop = loop; main = if (negate 1 >= 3) loop 3") (NodeInt 3)
  putChar '\n'
  where
    f = maybe undefined (f' . last . eval . compile) . parse
      where
        f' (_, [x], _, h, _) = H.lookup h x
        f' _ = undefined

tests :: IO ()
tests = do
  testCompile
  testEval
