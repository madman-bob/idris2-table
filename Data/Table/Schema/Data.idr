module Data.Table.Schema.Data

%default total

public export
data Schema : Type where
    Lin : Schema
    (:<) : Schema -> (String, Type) -> Schema

%name Schema schema

infix 10 :!

public export
(:!) : String -> Type -> (String, Type)
(:!) = (,)

public export
names : Schema -> SnocList String
names [<] = [<]
names (schema :< (name, type)) = names schema :< name

public export
types : Schema -> SnocList Type
types [<] = [<]
types (schema :< (name, type)) = types schema :< type

public export
data Field : (schema : Schema) -> (name : String) -> Type -> Type where [search schema name]
    Here : Field (schema :< (name, type)) name type
    There : (fld : Field schema name type) -> Field (schema :< (n, t)) name type

%name Field fld

public export
(++) : Schema -> Schema -> Schema
schema1 ++ [<] = schema1
schema1 ++ (schema2 :< hdr) = (schema1 ++ schema2) :< hdr
