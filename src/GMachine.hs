{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}

module GMachine where

import qualified Data.IntMap.Strict as I
import Data.List (mapAccumL)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
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
  | InstPack Int Int
  | InstCaseJump (I.IntMap [Inst])
  | InstSplit Int
  | InstPushUndef
  deriving (Eq, Show)

data Node
  = NodeInt Int
  | NodeApp H.Addr H.Addr
  | NodeGlobal Int [Inst]
  | NodeIndir H.Addr
  | NodeData Int [H.Addr]
  | NodeUndef
  deriving (Eq, Show)

type Frame = ([Inst], [H.Addr])

type Globals = M.Map String H.Addr

type State = ([Inst], [H.Addr], [Frame], H.Heap Node, Globals)

type Compiler = Expr String -> M.Map String Int -> [Inst]

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
dispatch (InstPack t n) = pack t n
dispatch (InstCaseJump as) = caseJump as
dispatch (InstSplit n) = split n
dispatch InstEval = eval'
dispatch InstPushUndef = pushUndef

toInt :: Bool -> Int
toInt True = 1
toInt False = 0

pushGlobal :: String -> State -> State
pushGlobal s (is, as, fs, h, gs) = (is, (M.!) gs s : as, fs, h, gs)

pushInt :: Int -> State -> State
pushInt n (is, as, fs, h, gs) =
  if M.member s gs
    then (is, (M.!) gs s : as, fs, h, gs)
    else
      let (h', a) = H.alloc h (NodeInt n)
       in (is, a : as, fs, h', M.insert s a gs)
  where
    s = show n

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
    NodeUndef -> undefined
    NodeInt _ -> (is'', a : as'', fs, h, gs)
    NodeData _ _ -> (is'', a : as'', fs, h, gs)
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

pushUndef :: State -> State
pushUndef (is, as, fs, h, gs) =
  if M.member s gs
    then (is, (M.!) gs s : as, fs, h, gs)
    else
      let (h', a) = H.alloc h NodeUndef
       in (is, a : as, fs, h', M.insert s a gs)
  where
    s = "undef"

rearrange :: Int -> H.Heap Node -> [H.Addr] -> [H.Addr]
rearrange n h as = take n (map (f . H.lookup h) $ tail as) ++ drop n as
  where
    f (NodeApp _ a) = a
    f _ = undefined

pack :: Int -> Int -> State -> State
pack t n (is, as, fs, h, gs) =
  if length as < n
    then undefined
    else (is, a : drop n as, fs, h', gs)
  where
    (h', a) = H.alloc h (NodeData t $ take n as)

caseJump :: I.IntMap [Inst] -> State -> State
caseJump m (is, as@(a : _), fs, h, gs) =
  case H.lookup h a of
    NodeData t _ -> ((I.!) m t ++ is, as, fs, h, gs)
    _ -> undefined
caseJump _ _ = undefined

split :: Int -> State -> State
split n (is, a : as, fs, h, gs) =
  case H.lookup h a of
    (NodeData _ as') ->
      if n < length as'
        then undefined
        else (is, take n as' ++ as, fs, h, gs)
    _ -> undefined
split _ _ = undefined

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
compileUnwind :: Compiler
compileUnwind e m =
  compileStrictExpr e m ++ [InstUpdate n, InstPop n, InstUnwind]
  where
    n = M.size m

compileData :: Expr String -> M.Map String Int -> Maybe [Inst]
compileData (ExprApp (ExprData t n) e) m =
  Just $ compileLazyExpr e m ++ [InstPack t n]
compileData (ExprApp e0@(ExprApp _ _) e1) m =
  (compileLazyExpr e1 m ++) <$> compileData e0 (offset 1 m)
compileData _ _ = Nothing

-- NOTE: `C`
compileLazyExpr :: Compiler
compileLazyExpr ExprUndef _ = [InstPushUndef]
compileLazyExpr (ExprVar s) m =
  if M.member s m
    then [InstPush $ (M.!) m s]
    else [InstPushGlobal s]
compileLazyExpr (ExprInt n) _ = [InstPushInt n]
compileLazyExpr (ExprLet r ds e) m =
  (if r then compileLetRec else compileLet) compileLazyExpr ds e m
compileLazyExpr (ExprData t 0) _ = [InstPack t 0]
compileLazyExpr e@(ExprApp e0 e1) m =
  fromMaybe
    (compileLazyExpr e1 m ++ compileLazyExpr e0 (offset 1 m) ++ [InstMkApp])
    (compileData e m)
compileLazyExpr _ _ = undefined

-- NOTE: `E`
compileStrictExpr :: Compiler
compileStrictExpr ExprUndef _ = [InstPushUndef]
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
compileStrictExpr (ExprCase e as) m =
  compileStrictExpr e m ++ [InstCaseJump $ compileAlts as m]
compileStrictExpr e@(ExprApp _ _) m =
  fromMaybe (compileLazyExpr e m ++ [InstEval]) (compileData e m)
compileStrictExpr e m = compileLazyExpr e m ++ [InstEval]

compileLetRec :: Compiler -> [(String, Expr String)] -> Compiler
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

compileLet :: Compiler -> [(String, Expr String)] -> Compiler
compileLet c ds e m =
  f ds m ++ c e (compileArgs ds m) ++ [InstSlide $ length ds]
  where
    f :: [(String, Expr String)] -> M.Map String Int -> [Inst]
    f [] _ = []
    f ((_, e') : ds') m' = compileLazyExpr e' m' ++ f ds' (offset 1 m')

compileAlts ::
  [(Int, [String], Expr String)] -> M.Map String Int -> I.IntMap [Inst]
compileAlts as m = I.fromList $ map f as
  where
    f (t, ns, e) =
      ( t,
        [InstSplit n]
          ++ compileStrictExpr
            e
            (M.union (M.fromList $ zip ns [0 ..]) $ offset n m)
          ++ [InstSlide n]
      )
      where
        n = length ns

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
      [InstPush 0, InstEval, InstNeg, InstUpdate 1, InstPop 1, InstUnwind]
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
  TEST
    (f "f = Pack {2, 2} 1 2")
    ( Just
        [ ( "f",
            0,
            [ InstPushInt 2,
              InstPushInt 1,
              InstPack 2 2,
              InstUpdate 0,
              InstPop 0,
              InstUnwind
            ]
          )
        ]
    )
  TEST
    (f "f = 1 + undef")
    ( Just
        [ ( "f",
            0,
            [ InstPushUndef,
              InstPushInt 1,
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
  TEST (f "twice f = compose f f; main = twice twice id 3") (NodeInt 3)
  TEST (f "f g h x = (g x) (h x); main = f const const 3") (NodeInt 3)
  TEST (f "twice f = compose f f; main = twice (id id id) 3") (NodeInt 3)
  TEST (f "main = const 3 undef") (NodeInt 3)
  TEST (f "main = const id undef 1") (NodeInt 1)
  TEST (f "h x y = g x y; g x = f x; f = const id; main = h 1 2") (NodeInt 2)
  TEST
    ( f $
        unlines
          [ "pair x y f = f x y;",
            "fst p = p id;",
            "snd p = p (const id);",
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
  TEST (f "main = let f = id id id in f f 3") (NodeInt 3)
  TEST
    ( f $
        unlines
          [ "consFn a b cc n = cc a b;",
            "hd list = list const undef;",
            "tl list = list (const id) undef;",
            "infinite x = letrec xs = consFn x xs in xs;",
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
  TEST
    (f "fac n = if (n == 0) 1 (n * fac (n - 1)); main = fac 5")
    (NodeInt 120)
  TEST
    ( f $
        unlines
          [ "gcd a b =",
            "  if (a == b)",
            "    a",
            "    if (a < b) (gcd b a) (gcd b (a - b));",
            "main = gcd 6 10"
          ]
    )
    (NodeInt 2)
  TEST (f "main = sum nil") (NodeInt 0)
  TEST (f "main = sum (cons 1 (cons 1 nil))") (NodeInt 2)
  TEST (f "ones = cons 1 ones; main = sum (take 10 ones)") (NodeInt 10)
  TEST
    ( f $
        unlines
          [ "ones = cons 1 ones;",
            "sumZip l r =",
            "  case l of",
            "    <1>      -> 0;",
            "    <2> x xs ->",
            "      case r of",
            "        <1>      -> 0;",
            "        <2> y ys -> x + y + sumZip xs ys;",
            "main = sumZip ones (cons 1 (cons 2 (cons 3 nil)))"
          ]
    )
    (NodeInt 9)
  TEST
    ( f $
        unlines
          [ "loop n = if (n == 0) n (n + (loop (n - 1)));",
            "main = loop 10"
          ]
    )
    (NodeInt 55)
  TEST
    ( f $
        unlines
          [ "ackermannPeter m n =",
            "  if (m == 0)",
            "    (n + 1)",
            "    (if (n == 0)",
            "      (ackermannPeter (m - 1) 1)",
            "      (ackermannPeter (m - 1) (ackermannPeter m (n - 1))));",
            "main = ackermannPeter 2 1"
          ]
    )
    (NodeInt 5)
  TEST
    ( f $
        unlines
          [ "zipWith f l r =",
            "  case l of",
            "    <1>      -> nil;",
            "    <2> x xs ->",
            "      case r of",
            "        <1>      -> nil;",
            "        <2> y ys -> cons (f x y) (zipWith f xs ys);",
            "add x y = x + y;",
            "main =",
            "  letrec",
            "    fibs = cons 0 (cons 1 (zipWith add fibs (tail fibs)))",
            "  in",
            "  negate (head (drop 10 fibs))"
          ]
    )
    (NodeInt (-55))
  TEST
    ( f $
        unlines
          [ "main = ",
            "  letrec",
            "    x = 1;",
            "    xs = cons x (cons 2 (cons 3 xs))",
            "  in",
            "  sum (take 10 xs)"
          ]
    )
    (NodeInt 19)
  TEST
    ( f $
        unlines
          [ "c0 a b c = Pack {1, 3} a b c;",
            "c1 a b c d = Pack {2, 4} a b c d;",
            "f x =",
            "  case x of",
            "    <1> a b c   -> (a - b) + c;",
            "    <2> a b c d -> ((a - b) + c) - d;",
            "main =",
            "  let",
            "    x = c0 1 2 3;",
            "    y = c1 1 2 3 4",
            "  in",
            "  (f x) + (f y)"
          ]
    )
    (NodeInt 0)
  TEST (f "f x = if (1 == x) x; main = f 1 undef") (NodeInt 1)
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
