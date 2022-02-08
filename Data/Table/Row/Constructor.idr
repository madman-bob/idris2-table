module Data.Table.Row.Constructor

import public Data.Table.Data
import public Data.Table.Row.HasRows

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

infixl 7 |+|

public export
(|+|) : (tbl1 : Table schema1)
     -> (0 nrows1 : HasRows tbl1 n)
     => (tbl2 : Table schema2)
     -> (0 nrows2 : HasRows tbl2 n)
     => Table (schema1 ++ schema2)
([<] |+| [<]) {nrows1 = EmptyTable} {nrows2 = EmptyTable} = [<]
((tbl1 :< rec1) |+| (tbl2 :< rec2)) {nrows1 = SnocTable _} {nrows2 = SnocTable _} =
    (tbl1 |+| tbl2) :< (rec1 ++ rec2)

public export
zipHasRows : (0 tbl1 : Table schema1)
          -> (nrows1 : HasRows tbl1 n)
          => (0 tbl2 : Table schema2)
          -> (nrows2 : HasRows tbl2 n)
          => HasRows (tbl1 |+| tbl2) n
zipHasRows [<] [<] {nrows1 = EmptyTable} {nrows2 = EmptyTable} = EmptyTable
zipHasRows (tbl1 :< rec1) (tbl2 :< rec2) {nrows1 = SnocTable _} {nrows2 = SnocTable _} =
    SnocTable $ zipHasRows tbl1 tbl2
