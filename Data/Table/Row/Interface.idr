module Data.Table.Row.Interface

import Data.Nat
import Data.DPair
import Data.SnocList

import public Data.Table.Data
import public Data.Table.Row.HasRows

public export
(++) : Table schema -> Table schema -> Table schema
t ++ [<] = t
t ++ (rows :< rec) = (t ++ rows) :< rec

public export
concatHasRows : (0 tbl1 : Table schema)
             -> (hasRows1 : HasRows tbl1 n1)
             => (0 tbl2 : Table schema)
             -> (hasRows2 : HasRows tbl2 n2)
             => HasRows (tbl1 ++ tbl2) (n1 + n2)
concatHasRows tbl1 [<] {hasRows2 = EmptyTable} =
    replace {p = HasRows _} (sym $ plusZeroRightNeutral _) $
    hasRows1
concatHasRows tbl1 (tbl2 :< rec) {hasRows2 = SnocTable hasRows} =
    replace {p = HasRows _} (plusSuccRightSucc _ _) $
    SnocTable (concatHasRows tbl1 tbl2)

-- Algebra

public export
Semigroup (Table schema) where
    (<+>) = (++)

public export
Monoid (Table schema) where
    neutral = [<]

-- "Functor"

namespace SnocList
    public export
    map : (Record schema -> a) -> Table schema -> SnocList a
    map f [<] = [<]
    map f (tbl :< rec) = map f tbl :< f rec

    public export
    mapPreservesLength : HasRows tbl n => HasRows tbl (length (map f tbl))
    mapPreservesLength @{EmptyTable} = EmptyTable
    mapPreservesLength @{SnocTable _} = SnocTable mapPreservesLength

namespace Table
    public export
    map : (Record schema1 -> Record schema2) -> Table schema1 -> Table schema2
    map f [<] = [<]
    map f (tbl :< rec) = map f tbl :< f rec

    public export
    mapPreservesLength : HasRows tbl n => HasRows (map f tbl) n
    mapPreservesLength @{EmptyTable} = EmptyTable
    mapPreservesLength @{SnocTable _} = SnocTable Table.mapPreservesLength

-- "Foldable"

public export
foldr : (Record schema -> a -> a) -> a -> Table schema -> a
foldr f x [<] = x
foldr f x (tbl :< rec) = foldr f (f rec x) tbl

public export
toSnocList : Table schema -> SnocList (Record schema)
toSnocList [<] = [<]
toSnocList (tbl :< rec) = toSnocList tbl :< rec

public export
elemBy : (Record schema -> Record schema -> Bool) -> Record schema -> Table schema -> Bool
elemBy f rec tbl = elemBy f rec (toSnocList tbl)

public export
elem : Eq (Record schema) => Record schema -> Table schema -> Bool
elem = elemBy (==)

-- "Monad"

public export
pure : Record schema -> Table schema
pure rec = [<rec]

public export
pureHasRows : HasRows (pure rec) 1
pureHasRows = SnocTable EmptyTable

public export
(>>=) : Table schema1 -> (Record schema1 -> Table schema2) -> Table schema2
tbl >>= f = concat $ map f tbl

public export
bindHasRows : (tbl : Table schema1)
           -> (fHasRows : (rec : Record schema1) -> (Exists (HasRows (f rec))))
           -> HasRows (tbl >>= f) (sum $ map (\rec => (fHasRows rec).fst) tbl)
bindHasRows tbl fHasRows = partialSumHasRows tbl
  where
    partialSumHasRows : (tbl : Table schema1)
                     -> HasRows acc accRows
                     => HasRows (foldr (++) acc (map f tbl)) (foldr (+) accRows (map (\rec => (fHasRows rec).fst) tbl))
    partialSumHasRows [<] @{accHasRows} = accHasRows
    partialSumHasRows (tbl :< rec) = partialSumHasRows tbl @{concatHasRows _ @{(fHasRows rec).snd} _}

namespace HasRows
    public export
    (>>=) : (tbl : Table schema1)
         -> (fHasRows : (rec : Record schema1) -> (Exists (HasRows (f rec))))
         -> HasRows (tbl >>= f) (sum $ map (\rec => (fHasRows rec).fst) tbl)
    (>>=) = bindHasRows

public export
bindConstHasRows : (0 tbl : Table schema1)
                -> HasRows tbl m
                => (fHasRows : (0 rec : Record schema1) -> HasRows (f rec) n)
                -> HasRows (tbl >>= f) (m * n)
bindConstHasRows tbl fHasRows =
    replace {p = HasRows _} (plusZeroRightNeutral _) $
    partialSumHasRows tbl
  where
    partialSumHasRows : (0 tbl : Table schema1)
                     -> HasRows tbl p
                     => HasRows acc accRows
                     => HasRows (foldr (++) acc (map f tbl)) (p * n + accRows)
    partialSumHasRows [<] @{EmptyTable} @{accHasRows} = accHasRows
    partialSumHasRows (tbl :< rec) @{SnocTable hasRows} =
        replace {p = HasRows _} (trans (plusAssociative _ _ _) $ cong (+ accRows) $ plusCommutative _ _) $
        partialSumHasRows tbl @{hasRows} @{concatHasRows _ _}

namespace HasRowsConst
    public export
    (>>=) : (0 tbl : Table schema1)
         -> HasRows tbl m
         => (fHasRows : (0 rec : Record schema1) -> HasRows (f rec) n)
         -> HasRows (tbl >>= f) (m * n)
    (>>=) = bindConstHasRows
