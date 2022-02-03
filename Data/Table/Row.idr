module Data.Table.Row

import public Data.SnocList

import public Data.Table.Data
import public Data.Table.Row.Frame
import public Data.Table.Row.HasRows

%default total

public export
(++) : Table schema -> Table schema -> Table schema
t ++ [<] = t
t ++ (rows :< rec) = (t ++ rows) :< rec

namespace FromFoldable
    public export
    mkTable : Foldable f => f (Record schema) -> Table schema
    mkTable = foldl (:<) [<]

    public export
    (++) : Foldable f => Table schema -> f (Record schema) -> Table schema
    (++) = foldl (:<)

public export
map : (Record schema -> a) -> Table schema -> SnocList a
map f [<] = [<]
map f (tbl :< rec) = map f tbl :< f rec

export
mapPreservesLength : HasRows tbl n => HasRows tbl (length (map f tbl))
mapPreservesLength @{EmptyTable} = EmptyTable
mapPreservesLength @{SnocTable _} = SnocTable mapPreservesLength

public export
filter : (Record schema -> Bool) -> Table schema -> Table schema
filter f [<] = [<]
filter f (rows :< rec) =
    let rest = filter f rows in
    case f rec of
        False => rest
        True => rest :< rec
