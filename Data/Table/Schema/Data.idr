module Data.Table.Schema.Data

%default total

infix 10 :!

public export
data FieldSchema = (:!) String Type

%name FieldSchema fs

public export
data Schema : Type where
    Lin : Schema
    (:<) : Schema -> FieldSchema -> Schema

%name Schema schema

public export
(++) : Schema -> Schema -> Schema
s ++ [<] = s
s ++ (schema :< rec) = (s ++ schema) :< rec

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

%name Field fld
