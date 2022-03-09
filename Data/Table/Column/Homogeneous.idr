module Data.Table.Column.Homogeneous

import public Data.SnocList

import public Data.Table.Data
import public Data.Table.Schema.Quantifiers

%default total

public export
AllColumns : Schema -> Type -> Type
AllColumns schema type = AllTypes (=== type) schema

public export
allColumns : (schema : Schema)
          -> (0 _ : AllColumns schema type)
          => SnocList (name : String ** Field schema name type)
allColumns [<] = [<]
allColumns (schema :< (name :! type)) @{_ :< prf} =
    (map (\(n ** f) => (n ** There f)) $ allColumns schema) :< (name ** here prf)
