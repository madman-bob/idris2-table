module Data.Table.Schema.Data

%default total

infix 10 :!

public export
data FieldSchema = (:!) String Type

%name FieldSchema fs

public export
(.Name) : FieldSchema -> String
(name :! _).Name = name

public export
(.Sort) : FieldSchema -> Type
(_ :! sort).Sort = sort

public export
data Schema : Type where
    Lin : Schema
    (:<) : Schema -> FieldSchema -> Schema

%name Schema schema

public export
names : Schema -> SnocList String
names [<] = [<]
names (schema :< (name :! type)) = names schema :< name

public export
types : Schema -> SnocList Type
types [<] = [<]
types (schema :< (name :! type)) = types schema :< type

public export
length : Schema -> Nat
length [<] = 0
length (schema :< _) = S (length schema)

public export
data Field : (schema : Schema) -> (name : String) -> Type -> Type where [search schema name]
    Here : Field (schema :< (name :! type)) name type
    There : (fld : Field schema name type) -> Field (schema :< fs) name type

public export
weaken : Field schema name type -> Field (schema :< col) name type
weaken fld = There fld

%name Field fld

public export
(++) : Schema -> Schema -> Schema
schema1 ++ [<] = schema1
schema1 ++ (schema2 :< fs) = (schema1 ++ schema2) :< fs

public export
(.field) : {schema : Schema} -> Field schema name type -> FieldSchema
(Here).field {schema = _ :< fld@(_ :! _)} = fld
(There fld).field = fld.field
