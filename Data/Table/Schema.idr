module Data.Table.Schema

import public Data.Table.Schema.Data
import public Data.Table.Schema.Index
import public Data.Table.Schema.Subschema
import public Data.Table.Schema.Quantifiers

%default total

public export
fromString : (name : String)
          -> {auto fld : Field schema name type}
          -> Field schema name type
fromString name = fld

public export
replace : (schema : Schema)
       -> Field schema name type
       -> FieldSchema
       -> Schema
replace (schema :< (name :! type)) Here newFS = schema :< newFS
replace (schema :< fs) (There fld) newFS = replace schema fld newFS :< fs

public export
update : (schema : Schema)
      -> Field schema name type
      -> Type
      -> Schema
update (schema :< (name :! type)) Here newType = schema :< (name :! newType)
update (schema :< fs) (There fld) newType = update schema fld newType :< fs

public export
drop : (schema : Schema)
    -> Field schema name type
    -> Schema
drop (schema :< (name :! type)) Here = schema
drop (schema :< fs) (There fld) = drop schema fld :< fs
