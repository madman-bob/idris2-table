module Data.Table.Operations

import public Data.Table.Column
import public Data.Table.Data
import public Data.Table.Record
import public Data.Table.Row
import public Data.Table.Schema

public export
(|*|) : Table schema1 -> Table schema2 -> Table (schema1 |+| schema2)
[<] |*| table2 = [<]
(table1 :< rec) |*| table2 = (table1 |*| table2) ++ (rec |*| table2)

public export
0
crossJoinHasRows :
     (table1 : Table schema1)
  -> (hasRows1 : table1 `HasRows` n1)
  => (table2 : Table schema2)
  -> (hasRows2 : table2 `HasRows` n2)
  => (table1 |*| table2) `HasRows` n1 * n2
crossJoinHasRows [<] table2 {hasRows1 = EmptyTable} = EmptyTable
crossJoinHasRows (table1 :< rec) table2 {hasRows1 = SnocTable hasRows1}
  = let u1 = crossJoinHasRows table1 table2
        u2 = crossJoinHasRows rec    table2
    in (vcatHasRows (table1 |*| table2) (rec |*| table2))
    `ByProof` (plusCommutative _ _)

namespace Record
  public export
  (|*|) : Record schema1 -> Frame schema2 n -> Frame (schema1 |+| schema2) n
  rec |*| frame = (rec |*| frame.fst) `Element`
    (let 0 u = frame.snd in
    (crossJoinHasRows rec frame.fst))

namespace Frame
  public export
  (|*|) : Frame schema1 n1 -> Frame schema2 n2
    -> Frame (schema1 |+| schema2) (n1*n2)
  frame1 |*| frame2 =
    let 0 hasRows1 = frame1.snd
        0 hasRows2 = frame2.snd
    in (frame1.fst |*| frame2.fst)
         `Element`
       (crossJoinHasRows frame1.fst frame2.fst)
