module Data.Table.Row.Constructor

import public Data.Table.Data

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
