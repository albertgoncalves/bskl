{-# LANGUAGE Strict #-}

module Lang where

type IsRec = Bool

data Expr a
  = ExprVar String
  | ExprInt Int
  | ExprData Int Int
  | ExprApp (Expr a) (Expr a)
  | ExprLet IsRec [(a, Expr a)] (Expr a)
  | ExprCase (Expr a) [(Int, [a], Expr a)]
  | ExprLam [a] (Expr a)
  | ExprUndef
  deriving (Eq, Show)

isAtomic :: Expr a -> Bool
isAtomic (ExprVar _) = True
isAtomic (ExprInt _) = True
isAtomic _ = False

type Func = (String, [String], Expr String)

type Program = [Func]

prelude :: Program
prelude =
  [ ("I", ["x"], ExprVar "x"),
    ("K", ["x", "y"], ExprVar "x"),
    ("K1", ["x", "y"], ExprVar "y"),
    ( "S",
      ["f", "g", "x"],
      ExprApp
        (ExprApp (ExprVar "f") (ExprVar "x"))
        (ExprApp (ExprVar "g") (ExprVar "x"))
    ),
    ( "compose",
      ["f", "g", "x"],
      ExprApp
        (ExprVar "f")
        (ExprApp (ExprVar "g") (ExprVar "x"))
    ),
    ( "twice",
      ["f"],
      ExprApp
        (ExprApp (ExprVar "compose") (ExprVar "f"))
        (ExprVar "f")
    ),
    ("nil", [], ExprData 1 0),
    ( "cons",
      ["x", "xs"],
      ExprApp (ExprApp (ExprData 2 2) (ExprVar "x")) (ExprVar "xs")
    )
  ]
