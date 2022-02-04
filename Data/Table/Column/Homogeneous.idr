module Data.Table.Column.Homogeneous

import public Data.SnocList

import public Data.Table.Data

%default total

public export
data AllColumns : (schema : Schema) -> (type : Type) -> Type where [search schema]
    Z : AllColumns [<] a
    S : AllColumns schema a -> AllColumns (schema :< (name, a)) a

public export
allColumns : (schema : Schema)
          -> AllColumns schema type
          => SnocList (name : String ** HasField schema name type)
allColumns [<] = [<]
allColumns (schema :< (name, type)) @{S _} =
    (map (\(n ** p) => (n ** There p)) $ allColumns schema) :< (name ** Here)
