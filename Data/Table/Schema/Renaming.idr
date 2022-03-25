module Data.Table.Schema.Renaming

import public Data.Table.Schema.Data
import public Data.Table.Schema.Quantifiers
import public Data.Table.Schema.Properties
import public Data.Table.Row

import Syntax.PreorderReasoning

%default total

public export
Ren : (src, tgt : Schema) -> Type
Ren src tgt = All (\fld => tgt `FieldTyped` fld.Sort) src

infixl 7 :<.

||| Smart constructor for records that uses eta on the field
public export
(:<.) : Record schema -> fld.Sort -> Record (schema :< fld)
(rec :<. x) {fld = _ :! _} = rec `Record.(:<)` x

apply : Ren schema1 schema2 -> Field schema1 name type  -> FieldTyped schema2 type
apply (_   :< fld) Here = fld
apply (rho :< _  ) (There fld) = apply rho fld

public export
Apply : Ren schema1 schema2 -> FieldTyped schema1 type  -> FieldTyped schema2 type
Apply rho fld = apply rho fld.snd

-- We'll use `Apply` in infix notation much
infixr 4 `Apply`

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
ComposeRen : (rho2 : Ren schema2 schema3) -> (rho1 : Ren schema1 schema2) ->
  Ren schema1 schema3
ComposeRen rho2 [<] = [<]
ComposeRen rho2 (rho1 :< fld) = (ComposeRen rho2 rho1) :< (apply rho2 fld.snd)

export
applyMap : (f : forall type. FieldTyped schema2 type -> FieldTyped schema3 type) -> 
     (rho : Ren schema1 schema2) ->
     (fld : Field schema1 name type) -> 
     Renaming.apply (map f rho) fld === f (apply rho fld)
applyMap f (rho :< pos) Here = Refl
applyMap f (rho :< pos) (There fld) = applyMap f rho fld


export
applyIdId : {schema : Schema} -> (fld : Field schema name type) -> 
  apply IdRen fld === Evidence name fld
applyIdId Here = Refl
applyIdId (There fld) {schema = schema :< fs@(_ :! _)} = 
  let f : forall type. FieldTyped schema type -> FieldTyped ? type
      f x = Evidence x.fst $ There {fs} x.snd
  in Calc $
  |~ apply (map (\x => Evidence x.fst $ There {fs} x.snd) (IdRen {schema})) fld
  ~~ f (apply IdRen fld)       ...(applyMap f (IdRen {schema}) fld)
  ~~ Evidence name (There fld) ...(cong f $ applyIdId fld)

export
ApplyIdId : {schema : Schema} -> (fld : FieldTyped schema type) -> 
  Apply IdRen fld === fld
ApplyIdId (Evidence name fld) = applyIdId fld

export
renExtensionality : (rho1, rho2 : Ren schema1 schema2) ->
  (forall type. (fld : FieldTyped schema1 type) -> apply rho1 fld.snd = apply rho2 fld.snd) -> rho1 = rho2
renExtensionality  [<] [<] f = Refl
renExtensionality  (rho1 :< fld1) (rho2 :< fld2) {schema1 = schema1 :< (name :! type)} f
   = cong2 (:<) 
     (renExtensionality rho1 rho2 $ \fld => f $ Evidence fld.fst $ There fld.snd)
     (f (Evidence name Here))

applyComposeRenApply : (rho2 : Ren schema2 schema3) -> (rho1 : Ren schema1 schema2) ->
  (fld : Field schema1 name type) ->
  (rho2 `ComposeRen` rho1) `apply` fld = rho2 `Apply` (rho1 `apply` fld)
applyComposeRenApply rho2 (rho1 :< fld) Here = Refl
applyComposeRenApply rho2 (rho1 :< _  ) (There fld) = applyComposeRenApply rho2 rho1 fld


export
ApplyComposeRenApply : (rho2 : Ren schema2 schema3) -> (rho1 : Ren schema1 schema2) ->
  (fld : FieldTyped schema1 type) ->
  (rho2 `ComposeRen` rho1) `Apply` fld = rho2 `Apply` (rho1 `Apply` fld)
ApplyComposeRenApply rho2 rho1 fld = applyComposeRenApply rho2 rho1 fld.snd


export
composeIdLeftNeutral : {schema2 : Schema} -> (rho : Ren schema1 schema2) ->
  (IdRen `ComposeRen` rho) === rho
composeIdLeftNeutral rho = renExtensionality _ _ $ \fld => Calc $
  |~ ((IdRen `ComposeRen` rho) `Apply` fld)
  ~~ IdRen `Apply` (rho `Apply` fld)      ...(ApplyComposeRenApply _ _ _)
  ~~ rho `Apply` fld                      ...(ApplyIdId _)

export
composeIdRightNeutral : {schema1 : Schema} -> (rho : Ren schema1 schema2) ->
  (rho `ComposeRen` IdRen) === rho
composeIdRightNeutral rho = renExtensionality _ _ $ \fld => Calc $
  |~ (rho `ComposeRen` IdRen) `Apply` fld
  ~~ rho `Apply` (IdRen `Apply` fld) ...(ApplyComposeRenApply _ _ _)
  ~~ rho `Apply` fld                 ...(cong (rho `Apply`) $ ApplyIdId _)

public export
weaken : {schema1, schema2 : Schema} ->
  Ren schema1 (schema1 ++ schema2)
weaken {schema1 = [<]} = [<]
weaken {schema1 = schema1 :< fld@(_ :! _)} =
  (replace {p = Ren schema1}
          (appendSchemaAssociative schema1 [<fld] schema2) $
          weaken {schema1, schema2 = [<fld] ++ schema2}
  ) :< Evidence fld.Name (weakenField schema2 Here)


