module Data.Table.Row.Interface

import Data.SnocList

import public Data.Table.Data
import public Data.Table.Row.HasRows

-- "Functor"

public export
map : (Record schema -> a) -> Table schema -> SnocList a
map f [<] = [<]
map f (tbl :< rec) = map f tbl :< f rec

public export
mapPreservesLength : HasRows tbl n => HasRows tbl (length (map f tbl))
mapPreservesLength @{EmptyTable} = EmptyTable
mapPreservesLength @{SnocTable _} = SnocTable mapPreservesLength

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
