module Data.Table.Schema.Subschema

import public Data.Table.Schema.Data
import public Data.Table.Schema.Quantifiers

%default total

public export
data Subschema : (subschema : Schema) -> (superschema : Schema) -> Type where [uniqueSearch, search superschema]
    Lin : Subschema [<] superschema
    (:<) : Subschema subschema init
        -> Concat schema (init :< fs) rest
        -> Subschema (subschema :< fs) schema

public export
complement : (schema : Schema)
          -> Subschema subschema schema
          -> Schema
complement schema [<] = schema
complement o@(schema :< fs) (ss :< c) with ()
  complement o@(schema :< fs) (ss :< ConcatLin) | _ = complement schema ss
  complement o@(schema :< fs) (ss :< ConcatSnoc d) | _ = complement schema (ss :< d) :< fs
