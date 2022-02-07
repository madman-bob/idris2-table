module Data.Table.Schema

import public Data.Table.Schema.Data
import public Data.Table.Schema.Index

%default total

public export
fromString : (name : String)
          -> {auto fld : Field schema name type}
          -> Field schema name type
fromString name = fld

public export
drop : (schema : Schema)
    -> Field schema name type
    -> Schema
drop (schema :< (name, type)) Here = schema
drop (schema :< (n, t)) (There fld) = drop schema fld :< (n, t)
