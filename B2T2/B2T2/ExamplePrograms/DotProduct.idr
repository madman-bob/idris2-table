module B2T2.ExamplePrograms.DotProduct

import public Data.Table

%default total

public export
dot : Num a
   => (0 c1 : String)
   -> HasField schema c1 a
   => (0 c2 : String)
   -> HasField schema c2 a
   => (tbl : Table schema)
   -> a
dot c1 c2 [<] = 0
dot c1 c2 (tbl :< rec) = dot c1 c2 tbl + field c1 rec * field c2 rec
