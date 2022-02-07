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
          => SnocList (name : String ** Field schema name type)
allColumns [<] = [<]
allColumns (schema :< (name, type)) @{S _} =
    (map (\(n ** f) => (n ** There f)) $ allColumns schema) :< (name ** Here)
