module B2T2.ExamplePrograms.DotProduct

import public Data.Table

%default total

public export
dot : Num a
   => Field schema c1 a
   -> Field schema c2 a
   -> Table schema
   -> a
dot f1 f2 [<] = 0
dot f1 f2 (tbl :< rec) = dot f1 f2 tbl + value f1 rec * value f2 rec
