module Data.Table.Record

import public Data.Table.Schema

%default total

public export
data Record : Schema -> Type where
    Lin : Record [<]
    (:<) : Record schema -> type -> Record (schema :< (name, type))

%name Record rec

public export
field : (0 name : String)
     -> HasField schema name type
     => Record schema
     -> type
field name @{Here} (rec :< x) = x
field name @{There pos} (rec :< x) = field name rec

public export
dropField : (0 name : String)
         -> HasField schema name type
         => Record schema
         -> Record (drop name schema)
dropField name @{Here} (rec :< x) = rec
dropField name @{There pos} (rec :< x) = dropField name rec :< x
