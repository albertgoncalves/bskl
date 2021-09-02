{-# LANGUAGE Strict #-}

module Test where

import System.Exit (exitFailure)
import Text.Printf (printf)

newtype Loc = Loc (String, Int)

test :: (Eq a, Show a) => Loc -> a -> a -> IO ()
test (Loc (file, line)) a b =
  if a == b
    then putChar '.'
    else do
      printf "!\n%s:%d\n" file line
      print a
      print b
      exitFailure
