module Data.Table.Schema.Subschema

import public Data.Table.Schema.Data
import public Data.Table.Schema.Quantifiers

%default total

public export
data Subschema : (subschema : Schema) -> (superschema : Schema) -> Type where [uniqueSearch, search superschema]
    Lin : Subschema [<] superschema
    (:<) : Subschema subschema init
        -> Initial schema (init :< fs)
        -> Subschema (subschema :< fs) schema

public export
complement : (schema : Schema)
          -> Subschema subschema schema
          -> Schema
complement schema [<] = schema
complement o@(schema :< fs) (ss :< i) with ()
  complement o@(schema :< fs) (ss :< WholeSchema) | _ = complement schema ss
  complement o@(schema :< fs) (ss :< InitialSchema j) | _ = complement schema (ss :< j) :< fs
