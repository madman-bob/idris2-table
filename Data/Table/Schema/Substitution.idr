module Data.Table.Schema.Substitution

import public Data.Table.Schema.Data
import public Data.Table.Schema.Quantifiers
import public Data.Table.Schema.Properties
import public Data.Table.Row

import Syntax.PreorderReasoning

%default total

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

export
applyMap : (f : forall type. FieldTyped schema2 type -> FieldTyped schema3 type) -> 
     (rho : Subst schema1 schema2) ->
     (fld : Field schema1 name type) -> 
     Substitution.apply (map f rho) fld === f (apply rho fld)
applyMap f (rho :< pos) Here = Refl
applyMap f (rho :< pos) (There fld) = applyMap f rho fld


export
applyIdId : {schema : Schema} -> (fld : Field schema name type) -> 
  apply IdSubst fld === Evidence name fld
applyIdId Here = Refl
applyIdId (There fld) {schema = schema :< fs@(_ :! _)} = 
  let f : forall type. FieldTyped schema type -> FieldTyped ? type
      f x = Evidence x.fst $ There {fs} x.snd
  in Calc $
  |~ apply (map (\x => Evidence x.fst $ There {fs} x.snd) (IdSubst {schema})) fld
  ~~ f (apply IdSubst fld)       ...(applyMap f (IdSubst {schema}) fld)
  ~~ Evidence name (There fld) ...(cong f $ applyIdId fld)

export
ApplyIdId : {schema : Schema} -> (fld : FieldTyped schema type) -> 
  Apply IdSubst fld === fld
ApplyIdId (Evidence name fld) = applyIdId fld

export
renExtensionality : (rho1, rho2 : Subst schema1 schema2) ->
  (forall type. (fld : FieldTyped schema1 type) -> apply rho1 fld.snd = apply rho2 fld.snd) -> rho1 = rho2
renExtensionality  [<] [<] f = Refl
renExtensionality  (rho1 :< fld1) (rho2 :< fld2) {schema1 = schema1 :< (name :! type)} f
   = cong2 (:<) 
     (renExtensionality rho1 rho2 $ \fld => f $ Evidence fld.fst $ There fld.snd)
     (f (Evidence name Here))

applyComposeSubstApply : (rho2 : Subst schema2 schema3) -> (rho1 : Subst schema1 schema2) ->
  (fld : Field schema1 name type) ->
  (rho2 `ComposeSubst` rho1) `apply` fld = rho2 `Apply` (rho1 `apply` fld)
applyComposeSubstApply rho2 (rho1 :< fld) Here = Refl
applyComposeSubstApply rho2 (rho1 :< _  ) (There fld) = applyComposeSubstApply rho2 rho1 fld


export
ApplyComposeSubstApply : (rho2 : Subst schema2 schema3) -> (rho1 : Subst schema1 schema2) ->
  (fld : FieldTyped schema1 type) ->
  (rho2 `ComposeSubst` rho1) `Apply` fld = rho2 `Apply` (rho1 `Apply` fld)
ApplyComposeSubstApply rho2 rho1 fld = applyComposeSubstApply rho2 rho1 fld.snd


export
composeIdLeftNeutral : {schema2 : Schema} -> (rho : Subst schema1 schema2) ->
  (IdSubst `ComposeSubst` rho) === rho
composeIdLeftNeutral rho = renExtensionality _ _ $ \fld => Calc $
  |~ ((IdSubst `ComposeSubst` rho) `Apply` fld)
  ~~ IdSubst `Apply` (rho `Apply` fld)      ...(ApplyComposeSubstApply _ _ _)
  ~~ rho `Apply` fld                      ...(ApplyIdId _)

export
composeIdRightNeutral : {schema1 : Schema} -> (rho : Subst schema1 schema2) ->
  (rho `ComposeSubst` IdSubst) === rho
composeIdRightNeutral rho = renExtensionality _ _ $ \fld => Calc $
  |~ (rho `ComposeSubst` IdSubst) `Apply` fld
  ~~ rho `Apply` (IdSubst `Apply` fld) ...(ApplyComposeSubstApply _ _ _)
  ~~ rho `Apply` fld                 ...(cong (rho `Apply`) $ ApplyIdId _)

public export
weaken : {schema1, schema2 : Schema} ->
  Subst schema1 (schema1 ++ schema2)
weaken {schema1 = [<]} = [<]
weaken {schema1 = schema1 :< fld@(_ :! _)} =
  (replace {p = Subst schema1}
          (appendSchemaAssociative schema1 [<fld] schema2) $
          weaken {schema1, schema2 = [<fld] ++ schema2}
  ) :< Evidence fld.Name (weakenField schema2 Here)


