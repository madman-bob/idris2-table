module Data.Table.Schema.Properties

import Data.Table.Schema.Data

export
appendSchemaAssociative : (schema1, schema2, schema3 : Schema) ->
  schema1 ++ (schema2 ++ schema3) = (schema1 ++ schema2) ++ schema3
appendSchemaAssociative schema1 schema2 [<] = Refl
appendSchemaAssociative schema1 schema2 (schema :< fs) = cong (:< fs)
  (appendSchemaAssociative schema1 schema2 schema)
