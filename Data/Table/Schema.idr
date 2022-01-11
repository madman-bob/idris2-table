module Data.Table.Schema

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
data HasField : (schema : Schema) -> (name : String) -> Type -> Type where [search schema name]
    Here : HasField (schema :< (name, type)) name type
    There : (pos : HasField schema name type) -> HasField (schema :< (n, t)) name type
