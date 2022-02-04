module Data.Table.Row.HasRows

import public Data.Fin
import public Data.Singleton

import public Data.Table.Data

%default total

public export
data HasRows : (tbl : Table schema) -> Nat -> Type where [search tbl]
    EmptyTable : HasRows [<] 0
    SnocTable : (hasRows : HasRows tbl n) -> HasRows (tbl :< rec) (S n)

namespace Singleton
    public export
    length : (0 tbl : Table schema) -> HasRows tbl n => Singleton n
    length [<] @{EmptyTable} = Val 0
    length (tbl :< _) @{SnocTable hasRows} = [| S (length tbl) |]

namespace HasRows
    public export
    length : (tbl : Table schema) -> (n : Nat ** HasRows tbl n)
    length [<] = (0 ** EmptyTable)
    length (tbl :< _) =
        let (m ** hasRows) = length tbl in
        (S m ** SnocTable hasRows)

public export
rowFromEnd : (tbl : Table schema)
          -> {auto 0 hasRows : HasRows tbl n}
          -> Fin n
          -> Record schema
rowFromEnd [<] {hasRows = EmptyTable} x = absurd x
rowFromEnd (tbl :< rec) FZ = rec
rowFromEnd (tbl :< rec) {hasRows = SnocTable _} (FS x) = rowFromEnd tbl x

public export
row : (tbl : Table schema)
   -> HasRows tbl n
   => Fin n
   -> Record schema
row tbl x =
    let Val _ = length tbl in
    rowFromEnd tbl $ complement x

public export
dropRows : (tbl : Table schema)
        -> HasRows tbl n
        => Fin (S n)
        -> Table schema
dropRows [<] @{EmptyTable} FZ = [<]
dropRows tbl@(_ :< _) @{SnocTable _} FZ = tbl
dropRows (tbl :< _) @{SnocTable _} (FS k) = dropRows tbl k

public export
init : (tbl : Table schema)
    -> HasRows tbl n
    => Fin (S n)
    -> Table schema
init tbl k =
    let Val _ = length tbl in
    dropRows tbl $ complement k
