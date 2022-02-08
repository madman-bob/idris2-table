module Data.Table.Row.Constructor

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

infixl 9 |*|

namespace Record
    public export
    (|*|) : Record schema1 -> Table schema2 -> Table (schema1 ++ schema2)
    rec1 |*| [<] = [<]
    rec1 |*| (tbl :< rec2) = (rec1 |*| tbl) :< (rec1 ++ rec2)

    public export
    crossJoinHasRows : (0 rec : Record schema1)
                    -> (0 tbl : Table schema2)
                    -> (hasRows : HasRows tbl n)
                    => HasRows (rec |*| tbl) n
    crossJoinHasRows _ [<] {hasRows = EmptyTable} = EmptyTable
    crossJoinHasRows rec (tbl :< _) {hasRows = SnocTable hasRows} = SnocTable (crossJoinHasRows rec tbl)

public export
(|*|) : Table schema1 -> Table schema2 -> Table (schema1 ++ schema2)
[<] |*| tbl2 = [<]
(tbl1 :< rec) |*| tbl2 = (tbl1 |*| tbl2) ++ (rec |*| tbl2)

public export
crossJoinHasRows : (0 tbl1 : Table schema1)
                -> (hasRows1 : HasRows tbl1 n1)
                => (0 tbl2 : Table schema2)
                -> (hasRows2 : HasRows tbl2 n2)
                => HasRows (tbl1 |*| tbl2) (n1 * n2)
crossJoinHasRows [<] _ {hasRows1 = EmptyTable} = EmptyTable
crossJoinHasRows (tbl1 :< rec) tbl2 {hasRows1 = SnocTable hasRows1} =
    let hasRows1 = crossJoinHasRows tbl1 tbl2
        hasRows2 = crossJoinHasRows rec tbl2 in
    replace {p = HasRows _} (plusCommutative _ _) $
    concatHasRows (tbl1 |*| tbl2) (rec |*| tbl2)
