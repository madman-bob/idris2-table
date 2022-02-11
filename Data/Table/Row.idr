module Data.Table.Row

import Data.List
import public Data.SnocList

import public Data.Table.Data
import public Data.Table.Row.Aggregate
import public Data.Table.Row.Constructor
import public Data.Table.Row.Frame
import public Data.Table.Row.HasRows

%default total

export
HasRowsProof : forall table.
     (hasRows : table `HasRows` n)
  -> (prf : n = m) -> (table `HasRows` m)
HasRowsProof {table} hasRows prf = replace {p = \k => table `HasRows` k} prf hasRows

public export
concatHasRows : {n1, n2 : _}
  -> (table1 : Table schema)
  -> (hasRows1 : table1 `HasRows` n1)
  => (table2 : Table schema)
  -> (hasRows2 : table2 `HasRows` n2)
  => table1 ++ table2 `HasRows` (n1 + n2)
concatHasRows table1 [<] {hasRows2 = EmptyTable}
  = hasRows1 `HasRowsProof` (sym $ plusZeroRightNeutral n1)
concatHasRows table1 (table2 :< rec) {hasRows2 = SnocTable hasRows}
  = (SnocTable (concatHasRows table1 table2))
    `HasRowsProof`
    (plusSuccRightSucc _ _)

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

public export
map : (Record schema -> a) -> Table schema -> SnocList a
map f [<] = [<]
map f (tbl :< rec) = map f tbl :< f rec

export
mapPreservesLength : HasRows tbl n => HasRows tbl (length (map f tbl))
mapPreservesLength @{EmptyTable} = EmptyTable
mapPreservesLength @{SnocTable _} = SnocTable mapPreservesLength

public export
foldr : (Record schema -> a -> a) -> a -> Table schema -> a
foldr f x [<] = x
foldr f x (tbl :< rec) = foldr f (f rec x) tbl

public export
distinctBy : (Record schema -> Record schema -> Bool) -> Table schema -> Table schema
distinctBy f tbl = foldl (\acc, rec => ifThenElse (elemBy f rec acc) acc (acc :< rec)) [<] $ toSnocList tbl

public export
distinct : Eq (Record schema) => Table schema -> Table schema
distinct = distinctBy (==)

export
sortBy : (Record schema -> Record schema -> Ordering) -> Table schema -> Table schema
sortBy cmp tbl = mkTable $ List.sortBy cmp (cast $ toSnocList tbl)

export
sort : Ord (Record schema) => Table schema -> Table schema
sort = sortBy compare

public export
filter : (Record schema -> Bool) -> Table schema -> Table schema
filter f [<] = [<]
filter f (rows :< rec) =
    let rest = filter f rows in
    case f rec of
        False => rest
        True => rest :< rec

infixl 9 |*|

public export
(|*|) : Record schema1 -> Table schema2 -> Table (schema1 ++ schema2)
rec1 |*| [<] = [<]
rec1 |*| (table :< rec2) = (rec1 |*| table) :< (rec1 ++ rec2)

public export
crossJoinHasRows :
     {n : Nat}
  -> (rec : Record schema1)
  -> (table : Table schema2)
  -> (hasRows : table `HasRows` n)
  => rec |*| table `HasRows` n
crossJoinHasRows _        [<]   {hasRows = EmptyTable} = EmptyTable
crossJoinHasRows rec (tbl :< _) {hasRows = SnocTable hasRows}
  = SnocTable (crossJoinHasRows rec tbl)
