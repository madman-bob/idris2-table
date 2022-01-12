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
           -> HasRows tbl n
           => Fin n
           -> Record schema
rowFromEnd [<] @{EmptyTable} x = absurd x
rowFromEnd (tbl :< rec) FZ = rec
rowFromEnd (tbl :< rec) @{SnocTable _} (FS x) = rowFromEnd tbl x

public export
row : (tbl : Table schema)
   -> HasRows tbl n
   => Fin n
   -> Record schema
row tbl x =
    let Val _ = length tbl in
    rowFromEnd tbl $ complement x
