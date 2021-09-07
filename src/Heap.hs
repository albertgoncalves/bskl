{-# LANGUAGE Strict #-}

module Heap where

import qualified Data.IntMap.Strict as M
import Text.Printf (printf)
import Prelude hiding (null)

newtype Addr = Addr {getAddr :: Int}
  deriving (Eq)

instance Show Addr where
  show (Addr i) = "#" ++ show i

data Heap a = Heap
  { getSize :: Int,
    getFreeAddr :: [Addr],
    getHeap :: M.IntMap a
  }

instance Show a => Show (Heap a) where
  show (Heap s (a : _) m) =
    printf "Heap (%s, [%s, ...], %s)" (show s) (show a) (show m)
  show (Heap s _ m) = printf "Heap (%s, [], %s)" (show s) (show m)

null :: Addr
null = Addr 0

isNull :: Addr -> Bool
isNull = (null ==)

empty :: Heap a
empty = Heap 0 (map Addr [1 .. 200]) M.empty

alloc :: Heap a -> a -> (Heap a, Addr)
alloc (Heap s (a : as) m) x =
  (Heap (s + 1) as (M.insert (getAddr a) x m), a)
alloc _ _ = undefined

update :: Heap a -> Addr -> a -> Heap a
update (Heap s as m) (Addr i) x = Heap s as (M.insert i x m)

free :: Heap a -> Addr -> Heap a
free (Heap s as m) (Addr i) =
  if M.member i m
    then Heap (s - 1) (Addr i : as) (M.delete i m)
    else undefined

lookup :: Heap a -> Addr -> a
lookup (Heap _ _ m) (Addr i) = (M.!) m i
