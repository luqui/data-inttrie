-------------------------------------------------------------
-- |
-- Module        : Data.IntTrie
-- Copyright     : (c) Luke Palmer 2010
-- License       : BSD3
--
-- Maintainer    : Luke Palmer <lrpalmer@gmail.com>
-- Stability     : experimental
-- Portability   : Haskell 2010
--
-- Provides a minimal infinite, lazy trie for integral types.
-- It intentionally leaves out ideas such as delete and
-- emptiness so that it can be used lazily, eg. as the target
-- of an infinite foldr.  Essentially its purpose is to be an
-- efficient implementation of a function from integral type,
-- given point-at-a-time modifications.
-------------------------------------------------------------

module Data.IntTrie 
    ( IntTrie, identity, apply, modify, modify', overwrite )
where

import Control.Applicative
import Data.Bits
import Data.Function (fix)

-- | A trie from integers to values of type a. 
-- 
-- Semantics: [[IntTrie a]] = Integer -> a
data IntTrie a = IntTrie (BitTrie a) a (BitTrie a)  -- negative, 0, positive

data BitTrie a = BitTrie a (BitTrie a) (BitTrie a)

instance Functor BitTrie where
    fmap f ~(BitTrie x l r) = BitTrie (f x) (fmap f l) (fmap f r)

instance Applicative BitTrie where
    pure x = fix (\g -> BitTrie x g g)
    ~(BitTrie f fl fr) <*> ~(BitTrie x xl xr) = BitTrie (f x) (fl <*> xl) (fr <*> xr)

instance Functor IntTrie where
    fmap f ~(IntTrie neg z pos) = IntTrie (fmap f neg) (f z) (fmap f pos)

instance Applicative IntTrie where
    pure x = IntTrie (pure x) x (pure x)
    IntTrie fneg fz fpos <*> IntTrie xneg xz xpos = 
        IntTrie (fneg <*> xneg) (fz xz) (fpos <*> xpos)

-- | Apply the trie to an argument.  This is the semantic map.
apply :: (Ord b, Num b, Bits b) => IntTrie a -> b -> a
apply ~(IntTrie neg z pos) x =
    case compare x 0 of
        LT -> applyPositive neg (-x)
        EQ -> z
        GT -> applyPositive pos x

applyPositive :: (Num b, Bits b) => BitTrie a -> b -> a
applyPositive ~(BitTrie one even odd) x
    | x == 1 = one
    | testBit x 0 = applyPositive odd (x `shiftR` 1)
    | otherwise   = applyPositive even (x `shiftR` 1)

-- | The identity trie.  
--
-- > apply identity = id
identity :: (Num a, Bits a) => IntTrie a
identity = IntTrie (fmap negate identityPositive) 0 identityPositive

identityPositive :: (Num a, Bits a) => BitTrie a
identityPositive = go
    where
    go = BitTrie 1 (fmap (`shiftL` 1) go) (fmap (\n -> (n `shiftL` 1) .|. 1) go)

-- | Modify the function at one point
--
-- > apply (modify x f t) i | i == x = f (apply t i)
-- >                        | otherwise = apply t i
modify :: (Ord b, Num b, Bits b) => b -> (a -> a) -> IntTrie a -> IntTrie a
modify x f ~(IntTrie neg z pos) =
    case compare x 0 of
        LT -> IntTrie (modifyPositive (-x) f neg) z pos
        EQ -> IntTrie neg (f z) pos
        GT -> IntTrie neg z (modifyPositive x f pos)

modifyPositive :: (Num b, Bits b) => b -> (a -> a) -> BitTrie a -> BitTrie a
modifyPositive x f ~(BitTrie one even odd)
    | x == 1      = BitTrie (f one) even odd
    | testBit x 0 = BitTrie one even (modifyPositive (x `shiftR` 1) f odd)
    | otherwise   = BitTrie one (modifyPositive (x `shiftR` 1) f even) odd


-- | Modify the function at one point (strict version)
modify' :: (Ord b, Num b, Bits b) => b -> (a -> a) -> IntTrie a -> IntTrie a
modify' x f (IntTrie neg z pos) =
    case compare x 0 of
        LT -> (IntTrie $! modifyPositive' (-x) f neg) z pos
        EQ -> (IntTrie neg $! f z) pos
        GT -> IntTrie neg z $! modifyPositive' x f pos

modifyPositive' :: (Num b, Bits b) => b -> (a -> a) -> BitTrie a -> BitTrie a
modifyPositive' x f (BitTrie one even odd)
    | x == 1      = (BitTrie $! f one) even odd
    | testBit x 0 = BitTrie one even $! modifyPositive' (x `shiftR` 1) f odd
    | otherwise   = (BitTrie one $! modifyPositive' (x `shiftR` 1) f even) odd


-- | Overwrite the function at one point
--
-- > overwrite i x = modify i (const x)
overwrite :: (Ord b, Num b, Bits b) => b -> a -> IntTrie a -> IntTrie a
overwrite i x = modify i (const x)
