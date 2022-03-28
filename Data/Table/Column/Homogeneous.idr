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
allColumns (schema :< (name :! type)) @{_ :< _} =
    (map (\(n ** f) => (n ** There f)) $ allColumns schema) :< (name ** here)
  where
    here : (0 _ : TypeHas (=== t1) (name :! t2)) => Field (schema :< (name :! t2)) name t1
    here @{TheTypeHas sameType} = replace {p = Field _ _} sameType Here
