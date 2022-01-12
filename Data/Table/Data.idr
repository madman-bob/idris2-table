module Data.Table.Data

import public Data.Table.Record
import public Data.Table.Schema

%default total

public export
data Table : Schema -> Type where
    Lin : Table schema
    (:<) : Table schema -> Record schema -> Table schema

%name Table tbl
