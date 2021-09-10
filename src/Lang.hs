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

type Func = (String, [String], Expr String)

type Program = [Func]

prelude :: Program
prelude =
  [ ("id", ["x"], ExprVar "x"),
    ("const", ["x", "y"], ExprVar "x"),
    ( "compose",
      ["f", "g", "x"],
      ExprApp
        (ExprVar "f")
        (ExprApp (ExprVar "g") (ExprVar "x"))
    ),
    ("nil", [], ExprData 1 0),
    ( "cons",
      ["x", "xs"],
      ExprApp (ExprApp (ExprData 2 2) (ExprVar "x")) (ExprVar "xs")
    ),
    ( "take",
      ["n", "xs"],
      ExprApp
        ( ExprApp
            ( ExprApp
                (ExprVar "if")
                (ExprApp (ExprApp (ExprVar "==") (ExprVar "n")) (ExprInt 0))
            )
            (ExprVar "nil")
        )
        ( ExprCase
            (ExprVar "xs")
            [ (1, [], ExprVar "nil"),
              ( 2,
                ["y", "ys"],
                ExprApp
                  (ExprApp (ExprVar "cons") (ExprVar "y"))
                  ( ExprApp
                      ( ExprApp
                          (ExprVar "take")
                          ( ExprApp
                              (ExprApp (ExprVar "-") (ExprVar "n"))
                              (ExprInt 1)
                          )
                      )
                      (ExprVar "ys")
                  )
              )
            ]
        )
    ),
    ( "drop",
      ["n", "xs"],
      ExprApp
        ( ExprApp
            ( ExprApp
                (ExprVar "if")
                (ExprApp (ExprApp (ExprVar "==") (ExprVar "n")) (ExprInt 0))
            )
            (ExprVar "xs")
        )
        ( ExprCase
            (ExprVar "xs")
            [ (1, [], ExprVar "nil"),
              ( 2,
                ["y", "ys"],
                ExprApp
                  ( ExprApp
                      (ExprVar "drop")
                      ( ExprApp
                          (ExprApp (ExprVar "-") (ExprVar "n"))
                          (ExprInt 1)
                      )
                  )
                  (ExprVar "ys")
              )
            ]
        )
    ),
    ( "sum",
      ["xs"],
      ExprCase
        (ExprVar "xs")
        [ (1, [], ExprInt 0),
          ( 2,
            ["y", "ys"],
            ExprApp
              (ExprApp (ExprVar "+") (ExprVar "y"))
              (ExprApp (ExprVar "sum") (ExprVar "ys"))
          )
        ]
    ),
    ( "head",
      ["xs"],
      ExprCase
        (ExprVar "xs")
        [(1, [], ExprUndef), (2, ["y", "ys"], ExprVar "y")]
    ),
    ( "tail",
      ["xs"],
      ExprCase
        (ExprVar "xs")
        [(1, [], ExprUndef), (2, ["y", "ys"], ExprVar "ys")]
    )
  ]
