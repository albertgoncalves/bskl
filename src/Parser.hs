{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}

module Parser where

import Data.Bifunctor (first)
import Data.Char (isAlpha, isDigit, isSpace)
import Data.List.NonEmpty (NonEmpty (..))
import Lang (Expr (..), Func, Program)
import Test (Loc (..), test)
import Prelude hiding (lex)

newtype Token = Token {getString :: NonEmpty Char}

instance Show Token where
  show (Token (c :| cs)) = c : cs

type Parser a = [Token] -> [(a, [Token])]

isVar :: Char -> Bool
isVar c = isAlpha c || isDigit c || (c == '_')

lex :: String -> [Token]
lex ('-' : '-' : cs) =
  case dropWhile (/= '\n') cs of
    (_ : cs') -> lex cs'
    [] -> []
lex (a : b : cs)
  | [a, b] `elem` ["==", "~=", ">=", "<=", "->"] = Token (a :| [b]) : lex cs
lex (c : cs)
  | isSpace c = lex cs
  | isDigit c =
    let (as, bs) = span isDigit cs
     in Token (c :| as) : lex bs
  | isAlpha c =
    let (as, bs) = span isVar cs
     in Token (c :| as) : lex bs
  | otherwise = Token (c :| []) : lex cs
lex [] = []

alt :: Parser a -> Parser a -> Parser a
alt p0 p1 ts = p0 ts ++ p1 ts

lift2 :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
lift2 f p0 p1 ts0 = do
  (t1, ts1) <- p0 ts0
  (t2, ts2) <- p1 ts1
  return (f t1 t2, ts2)

lift3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
lift3 f p0 p1 p2 ts0 = do
  (t1, ts1) <- p0 ts0
  (t2, ts2) <- p1 ts1
  (t3, ts3) <- p2 ts2
  return (f t1 t2 t3, ts3)

lift4 ::
  (a -> b -> c -> d -> e) ->
  Parser a ->
  Parser b ->
  Parser c ->
  Parser d ->
  Parser e
lift4 f p0 p1 p2 p3 ts0 = do
  (t1, ts1) <- p0 ts0
  (t2, ts2) <- p1 ts1
  (t3, ts3) <- p2 ts2
  (t4, ts4) <- p3 ts3
  return (f t1 t2 t3 t4, ts4)

many :: Parser a -> Parser [a]
many p = many1 p `alt` empty []

many1 :: Parser a -> Parser [a]
many1 p = lift2 (:) p (many p)

empty :: a -> Parser a
empty x ts = [(x, ts)]

apply :: Parser a -> (a -> b) -> Parser b
apply p f = (first f <$>) . p

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p0 p1 = lift2 (:) p0 (many $ lift2 (\_ x -> x) p1 p0)

satisfy :: (String -> Bool) -> Parser String
satisfy f (t : ts)
  | f s = [(s, ts)]
  where
    s = show t
satisfy _ _ = []

lit :: String -> Parser String
lit s = satisfy (== s)

int :: Parser Int
int = satisfy (all isDigit) `apply` read

keywords :: [String]
keywords = ["let", "letrec", "case", "in", "of", "Pack"]

var :: Parser String
var =
  satisfy
    (\s -> not (isDigit $ head s) && (s `notElem` keywords) && all isVar s)

program :: Parser Program
program = sepBy1 func (lit ";")

func :: Parser Func
func = lift4 (\v vs _ e -> (v, vs, e)) var (many var) (lit "=") expr

expr :: Parser (Expr String)
expr = let_ `alt` (case_ `alt` (lambda `alt` expr1))

let_ :: Parser (Expr String)
let_ = lift4 f (lit "let" `alt` lit "letrec") fns (lit "in") expr
  where
    f l ds _ e = ExprLet (l == "letrec") ds e

case_ :: Parser (Expr String)
case_ =
  lift4 (\_ e _ as -> ExprCase e as) (lit "case") expr (lit "of") branches

branches :: Parser [(Int, [String], Expr String)]
branches = sepBy1 branch (lit ";")

branch :: Parser (Int, [String], Expr String)
branch = lift4 (\t as _ e -> (t, as, e)) tag (many var) (lit "->") expr

tag :: Parser Int
tag = lift3 (\_ t _ -> t) (lit "<") int (lit ">")

lambda :: Parser (Expr String)
lambda =
  lift4 (\_ vs _ e -> ExprLam vs e) (lit "\\") (many1 var) (lit ".") expr

fn :: Parser (String, Expr String)
fn = lift3 (\v _ e -> (v, e)) var (lit "=") expr

fns :: Parser [(String, Expr String)]
fns = sepBy1 fn (lit ";")

assembleOp :: Expr String -> Maybe (String, Expr String) -> Expr String
assembleOp e Nothing = e
assembleOp e0 (Just (op, e1)) = ExprApp (ExprApp (ExprVar op) e0) e1

expr1 :: Parser (Expr String)
expr1 =
  lift2
    assembleOp
    expr2
    (lift2 (curry Just) (lit "|") expr1 `alt` empty Nothing)

expr2 :: Parser (Expr String)
expr2 =
  lift2
    assembleOp
    expr3
    (lift2 (curry Just) (lit "&") expr2 `alt` empty Nothing)

expr3 :: Parser (Expr String)
expr3 =
  lift2
    assembleOp
    expr4
    (lift2 (curry Just) p expr4 `alt` empty Nothing)
  where
    p = satisfy (`elem` ["==", "~=", ">=", "<=", "<", ">"])

expr4 :: Parser (Expr String)
expr4 = lift2 assembleOp expr5 (p0 `alt` (p1 `alt` empty Nothing))
  where
    p0 = lift2 (curry Just) (lit "+") expr4
    p1 = lift2 (curry Just) (lit "-") expr5

expr5 :: Parser (Expr String)
expr5 = lift2 assembleOp expr6 (p0 `alt` (p1 `alt` empty Nothing))
  where
    p0 = lift2 (curry Just) (lit "*") expr5
    p1 = lift2 (curry Just) (lit "/") expr6

expr6 :: Parser (Expr String)
expr6 = many1 atomic `apply` foldl1 ExprApp

atomic :: Parser (Expr String)
atomic =
  pack `alt` (parens `alt` ((var `apply` ExprVar) `alt` (int `apply` ExprInt)))

parens :: Parser (Expr String)
parens = lift3 (\_ e _ -> e) (lit "(") expr (lit ")")

pack :: Parser (Expr String)
pack = lift4 (\_ _ x _ -> x) (lit "Pack") (lit "{") tagArity (lit "}")

tagArity :: Parser (Expr String)
tagArity = lift3 (\t _ a -> ExprData t a) int (lit ",") int

syntax :: [Token] -> Maybe Program
syntax = f . program
  where
    f ((x, []) : _) = Just x
    f (_ : xs) = f xs
    f [] = Nothing

#define TEST test (Loc (__FILE__, __LINE__))

parse :: String -> Maybe Program
parse = syntax . lex

tests :: IO ()
tests = do
  TEST (map show $ lex "123abc 456==") ["123", "abc", "456", "=="]
  TEST
    (parse "f a b c = a * b + c")
    ( Just
        [ ( "f",
            ["a", "b", "c"],
            ExprApp
              ( ExprApp
                  (ExprVar "+")
                  (ExprApp (ExprApp (ExprVar "*") (ExprVar "a")) (ExprVar "b"))
              )
              (ExprVar "c")
          )
        ]
    )
  TEST
    (parse "-- ???\nf = x; g = y")
    (Just [("f", [], ExprVar "x"), ("g", [], ExprVar "y")])
  TEST
    (parse "f = let x = 1; y = x in y")
    ( Just
        [ ( "f",
            [],
            ExprLet False [("x", ExprInt 1), ("y", ExprVar "x")] (ExprVar "y")
          )
        ]
    )
  TEST
    (parse "f a b c = a + b * c")
    ( Just
        [ ( "f",
            ["a", "b", "c"],
            ExprApp
              (ExprApp (ExprVar "+") (ExprVar "a"))
              (ExprApp (ExprApp (ExprVar "*") (ExprVar "b")) (ExprVar "c"))
          )
        ]
    )
  TEST
    (parse "f a b c = a - b / c")
    ( Just
        [ ( "f",
            ["a", "b", "c"],
            ExprApp
              (ExprApp (ExprVar "-") (ExprVar "a"))
              (ExprApp (ExprApp (ExprVar "/") (ExprVar "b")) (ExprVar "c"))
          )
        ]
    )
  TEST (parse "f a b c = a - b + c") Nothing
  TEST (parse "f a b c = a / b * c") Nothing
  TEST
    (parse "f x = letrec g = \\y. letrec h = \\z. h (g z) in h y x in g 4")
    ( Just
        [ ( "f",
            ["x"],
            ExprLet
              True
              [ ( "g",
                  ExprLam
                    ["y"]
                    ( ExprLet
                        True
                        [ ( "h",
                            ExprLam
                              ["z"]
                              ( ExprApp
                                  (ExprVar "h")
                                  (ExprApp (ExprVar "g") (ExprVar "z"))
                              )
                          )
                        ]
                        ( ExprApp
                            (ExprApp (ExprVar "h") (ExprVar "y"))
                            (ExprVar "x")
                        )
                    )
                )
              ]
              (ExprApp (ExprVar "g") (ExprInt 4))
          )
        ]
    )
  TEST
    (parse "f a b = case a of <0> x -> x; <1> y -> y")
    ( Just
        [ ( "f",
            ["a", "b"],
            ExprCase
              (ExprVar "a")
              [(0, ["x"], ExprVar "x"), (1, ["y"], ExprVar "y")]
          )
        ]
    )
  TEST
    (parse "x = Pack {0, 2} 1 2")
    ( Just
        [("x", [], ExprApp (ExprApp (ExprData 0 2) (ExprInt 1)) (ExprInt 2))]
    )
  TEST
    (parse "f = (\\x y. x + y)")
    ( Just
        [ ( "f",
            [],
            ExprLam
              ["x", "y"]
              (ExprApp (ExprApp (ExprVar "+") (ExprVar "x")) (ExprVar "y"))
          )
        ]
    )
  putChar '\n'
