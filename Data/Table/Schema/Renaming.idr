module Data.Table.Schema.Renaming

import public Data.Table.Schema.Data
import public Data.Table.Schema.Quantifiers
import public Data.Table.Schema.Properties
import public Data.Table.Row

%default total

public export
Ren : (src, tgt : Schema) -> Type
Ren src tgt = All (\fld => tgt `FieldTyped` fld.Sort) src

infixl 7 :<.

||| Smart constructor for records that uses eta on the field
public export
(:<.) : Record schema -> fld.Sort -> Record (schema :< fld)
(rec :<. x) {fld = _ :! _} = rec `Record.(:<)` x

public export
(.project) : (rec : Record src) -> Ren tgt src -> Record tgt
rec.project [<] = [<]
rec.project (ren :< pos) = (rec.project ren) :<. (rec.project pos)


-- The category of renamings
public export
IdRen : {schema : Schema} -> Ren schema schema
IdRen {schema = [<]         } = [<]
IdRen {schema = schema :< fs@(name :! type)} =
  Schema.Quantifiers.map (\x => Evidence x.fst $ weakenField [<fs] x.snd) (IdRen {schema})
  :< (Evidence name Here)

public export
weaken : {schema1, schema2 : Schema} ->
  Ren schema1 (schema1 ++ schema2)
weaken {schema1 = [<]} = [<]
weaken {schema1 = schema1 :< fld@(_ :! _)} =
  (replace {p = Ren schema1}
          (appendSchemaAssociative schema1 [<fld] schema2) $
          weaken {schema1, schema2 = [<fld] ++ schema2}
  ) :< Evidence fld.Name (weakenField schema2 Here)


