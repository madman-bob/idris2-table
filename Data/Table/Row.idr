module Data.Table.Row

import Data.List
import public Data.SnocList

import public Data.Table.Data
import public Data.Table.Row.Aggregate
import public Data.Table.Row.Constructor
import public Data.Table.Row.Frame
import public Data.Table.Row.HasRows
import public Data.Table.Row.Interface

%default total

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
filter f tbl = do
    rec <- tbl
    case f rec of
        False => [<]
        True => pure rec

public export
dropNa : (fld : Field schema name (Maybe type))
      -> Table schema
      -> Table (update schema fld type)
dropNa fld tbl = do
    rec <- tbl
    case value fld rec of
        Nothing => [<]
        Just x => pure $ setField fld x rec
