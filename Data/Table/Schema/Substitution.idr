module Data.Table.Schema.Substitution

import public Data.Table.Schema.Data
import public Data.Table.Schema.Quantifiers
import public Data.Table.Schema.Properties
import public Data.Table.Row
import        Data.Table.Schema.Subschema

import Decidable.Equality

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


-- The category of substitutions
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

-- local independent coproducts via complements
public export
(.without) : {schema1 : Schema} ->
  Subst schema1 schema2 -> Field schema2 name type -> Schema
[<].without fld = [<]
(rho :< fld').without fld {schema1 = _ :< col} = case decEqHet fld'.snd fld of
    Yes prf   => rho.without fld
    No contra => rho.without fld :< col

public export
(.restrict) : {schema1 : Schema} ->
  (rho : Subst schema1 schema2) -> (fld : Field schema2 name type) ->
  Subst (rho.without fld) schema2
[<].restrict fld = [<]
(rho :< fld').restrict fld {schema1 = _ :< col} with (decEqHet fld'.snd fld)
 _ | Yes prf   = rho.restrict fld
 _ | No contra = rho.restrict fld :< fld'

public export
(.complementSchema) : {schema2 : Schema} -> Subst schema1 schema2 -> Schema
public export
(.complement) : {schema2 : Schema} -> (rho : Subst schema1 schema2) ->
  Subst rho.complementSchema schema2

[<]         .complementSchema = schema2
(rho :< fld).complementSchema = rho.complement.without  fld.snd

[<]         .complement       = IdSubst
(rho :< fld).complement       = rho.complement.restrict fld.snd

recallInitial : {schema2 : Schema} -> Initial schema2 schema1 -> Schema
recallInitial WholeSchema          = schema2
recallInitial (InitialSchema init) = recallInitial init

recallInitialSpec : {schema1 : Schema} -> (init : Initial schema1 schema2) ->
  recallInitial init = schema2
recallInitialSpec WholeSchema = Refl
recallInitialSpec (InitialSchema init) = recallInitialSpec init

projectAux : {schema1 : Schema} -> (init : Initial schema1 schema2) ->
  Subst (recallInitial init) schema1
projectAux  init with (recallInitial init)
 projectAux init | [<] = [<]
 projectAux init | (schema :< fs) = let u = projectAux init in ?h1 

cast : {schema1 : Schema} -> (init : Initial schema1 schema2) -> Subst schema2 schema1
cast WholeSchema = IdSubst
cast (InitialSchema init) = (weaken {schema2 = [< _]}) `ComposeSubst` (cast init)

{-
  We say that the following commuting square is _independent_ and
  write:

              rho1
  schema0   ------> schema1
      |                  |
  rho2|                  | theta1
      |             _|_  |
      v                  v
  schema2  -------> schema
           theta2

  when every fld : Field schema name type
  that's an element of theta1 and theta2 is
  also an element of schema0

  Hmm... probably too much of a distraction at the moment. Continue in
  the future...
-}

public export
(++) : {schema1', schema2' : Schema} -> Subst schema1 schema1' -> Subst schema2 schema2' -> 
  Subst (schema1 ++ schema2) (schema1' ++ schema2')
rho1 ++ [<] = weaken `ComposeSubst` rho1
(rho1 ++ (rho2 :< fld)) {schema2 = schema2 :< _ :! _} = rho1 ++ rho2 :< fld

0 blah : {schema2 : Schema} -> Subschema schema1 schema2 -> Subst schema1 schema2
blah [<] = [<]
blah (subsch :< i) =
    let u = cast i
        v = blah subsch
    in ?h1980


