module Data.Table.Schema.Substitution

import public Data.Table.Schema.Data
import public Data.Table.Schema.Quantifiers
import public Data.Table.Schema.Properties
import public Data.Table.Row

public export
Subst : (src, tgt : Schema) -> Type
Subst src tgt = All (\fld => tgt `FieldTyped` fld.Sort) src

infixl 7 :<.

||| Smart constructor for records that uses eta on the field
public export
(:<.) : Record schema -> fld.Sort -> Record (schema :< fld)
(rec :<. x) {fld = _ :! _} = rec `Record.(:<)` x

apply : Subst schema1 schema2 -> Field schema1 name type  -> FieldTyped schema2 type
apply (_   :< fld) Here = fld
apply (rho :< _  ) (There fld) = apply rho fld

public export
Apply : Subst schema1 schema2 -> FieldTyped schema1 type  -> FieldTyped schema2 type
Apply rho fld = apply rho fld.snd

-- We'll use `Apply` in infix notation much
infixr 4 `Apply`

public export
(.project) : (rec : Record src) -> Subst tgt src -> Record tgt
rec.project [<] = [<]
rec.project (ren :< pos) = (rec.project ren) :<. (rec.project pos)


-- The category of renamings
public export
IdSubst : {schema : Schema} -> Subst schema schema
IdSubst {schema = [<]         } = [<]
IdSubst {schema = schema :< fs@(name :! type)} =
  Schema.Quantifiers.map (\x => Evidence x.fst $ weakenField [<fs] x.snd) (IdSubst {schema})
  :< (Evidence name Here)

public export
ComposeSubst : (rho2 : Subst schema2 schema3) -> (rho1 : Subst schema1 schema2) ->
  Subst schema1 schema3
ComposeSubst rho2 [<] = [<]
ComposeSubst rho2 (rho1 :< fld) = (ComposeSubst rho2 rho1) :< (apply rho2 fld.snd)

public export
weaken : {schema1, schema2 : Schema} ->
  Subst schema1 (schema1 ++ schema2)
weaken {schema1 = [<]} = [<]
weaken {schema1 = schema1 :< fld@(_ :! _)} =
  (replace {p = Subst schema1}
          (appendSchemaAssociative schema1 [<fld] schema2) $
          weaken {schema1, schema2 = [<fld] ++ schema2}
  ) :< Evidence fld.Name (weakenField schema2 Here)


