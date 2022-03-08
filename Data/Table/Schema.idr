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

infixl 6 |-|, |!|

public export
(|-|) : Foldable f => (schema : Schema) -> f String -> Schema
[<]    |-| names = [<]
(schema :< fld) |-| names = if fld.Name `elem` names
  then (schema |-| names)
  else (schema |-| names) :< fld

public export
(|!|) : Foldable f => (schema : Schema) -> f String -> Schema
[<]    |!| names = [<]
(schema :< fld) |!| names = if fld.Name `elem` names
  then (schema |!| names) :< fld
  else (schema |!| names)

public export
data IsSnoc : Schema -> Type where
  ItIsSnoc : IsSnoc (schedma :< col)

public export
(.tail) : (schema : Schema) -> {auto 0 isSnoc : IsSnoc schema} -> FieldSchema
(_ :< col).tail {isSnoc = ItIsSnoc} = col
