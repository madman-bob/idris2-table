module Data.Table.Join

import public Data.Table.Column
import public Data.Table.Data
import public Data.Table.Record
import public Data.Table.Row
import public Data.Table.Row.Constructor
import Data.Table.Row.Interface
import public Data.Table.Schema
import public Data.Table.Schema.Quantifiers
import public Data.Table.Schema.Properties
import public Data.Table.Schema.Substitution

import public Data.List
import        Data.List.Elem
import public Data.SnocList.Operations
import public Data.SnocList.Quantifiers
import public Data.List.Quantifiers

import Data.Table.Show

import Syntax.WithProof

import Decidable.Decidable

%default total

public export
Reason : (0 prf : post === pre) -> Frame s post -> Frame s pre
Reason prf frm = replace {p = Frame s} prf frm

namespace Record
  public export
  (|*|) : Record schema1 -> Frame schema2 n -> Frame (schema1 ++ schema2) n
  rec |*| frame = Reason
                    (plusZeroRightNeutral _) $
                    ([< rec] `Element` %search) |*| frame

namespace Frame
  public export
  (|*|) : Frame schema1 n1 -> Frame schema2 n2
    -> Frame (schema1 ++ schema2) (n1*n2)
  frame1 |*| frame2 =
    let 0 hasRows1 = frame1.snd
        0 hasRows2 = frame2.snd
    in (frame1.fst |*| frame2.fst)
         `Element`
       (crossJoinHasRows frame1.fst frame2.fst)

public export
(|!|) : {schema : Schema} ->
  Foldable f => (rec : Record schema) -> (names : f String) -> Record (schema |!| names)
[<] |!| names = [<]
((rec :< fld) |!| names) with (schema.tail.Name `elem` names)
  _ | True  = (rec |!| names) :< fld
  _ | False = (rec |!| names)

public export
(|-|) : {schema : Schema} ->
  Foldable f => (rec : Record schema) -> (names : f String) -> Record (schema |-| names)
[<] |-| names = [<]
(rec :< fld) |-| names with (schema.tail.Name `elem` names)
 _ | True  = (rec |-| names)
 _ | False = (rec |-| names) :< fld


-- The idea: a record is a special kind of All
schemaMap : (p : FieldSchema -> FieldSchema) -> Schema -> Schema
schemaMap p [<] = [<]
schemaMap p (schema :< fs) = schemaMap p schema :< p fs

public export
mapSchema : (Type -> Type) -> Schema -> Schema
mapSchema f = schemaMap $ \fld => fld.Name :! f fld.Sort

public export
mapRecord : {0 f : Type -> Type} -> (c : forall a. a -> f a) -> Record schema ->
  Record (mapSchema f schema)
mapRecord c [<] = [<]
mapRecord c (rec :< fld) = mapRecord c rec :< c fld

allFwd : All (q . p) schema -> All q $ schemaMap p schema
allFwd [<] = [<]
allFwd (xs :< x) = allFwd xs :< x

schemaMapNilNil : {schema : Schema} -> (f : _) -> schemaMap f schema = [<] -> schema = [<]
schemaMapNilNil {schema = [<]         } f _ = Refl
schemaMapNilNil {schema = schema :< fs} f _ impossible

lemma : {schema : Schema} -> (p : _) -> Not (schemaMap p schema === [<]) -> IsSnoc schema
lemma {schema = [<]} p f = absurd $ f Refl
lemma {schema = schema :< fs@(_ :! _)} p f = ItIsSnoc

{schema : Schema} -> Uninhabited ((schema :< fld) === [<]) where
  uninhabited Refl impossible


snocFieldInjective : {0 schema1,schema2 : Schema} -> (schema1 :< fld1) = (schema2 :< fld2) -> (schema1 = schema2, fld1 = fld2)
snocFieldInjective Refl = (Refl, Refl)

recallEq : (0 prf : a = b) -> a = b
recallEq Refl = Refl

-- Ridiculous
allBwd : (x : All q schema') ->
  {auto 0 fordSchema : schema' = schemaMap p schema} ->
  All (q . p) schema
allBwd [<] with 0 (schemaMapNilNil p $ sym fordSchema)
 _ | Refl = [<]
allBwd  {schema} ((xs :< x) {col})
  with 0 (lemma p $ \prf => absurd $ trans fordSchema prf)
 allBwd {schema = (schema :< (name :! type))} ((xs :< x) {col = name :! type0})
   | ItIsSnoc =
     allBwd xs {fordSchema = fst $ snocFieldInjective fordSchema}
     :<
     replace {p = q} (recallEq $ snd $ snocFieldInjective fordSchema) x

allBwd' : (x : All q $ schemaMap p schema) ->
  All (q . p) schema
allBwd' x = allBwd x
-- the point: a Record is an All
recordAll : Record schema -> All (.Sort) schema
recordAll [<] = [<]
recordAll (rec :< x) = recordAll rec :< x

-- Now we can easily write record filters and mergers (I hope)

mapAnyAll : {0 schema : Schema} ->
  ((pos : Any p schema) -> q pos.field) -> All p schema -> All q schema
mapAnyAll f [<] = [<]
mapAnyAll f (xs :< x) = mapAnyAll (\ pos => f $ There pos) xs :< (f $ Here x)

mapAnyAny : {0 schema : Schema} ->
  ((pos : Any p schema) -> q pos.field) -> Any p schema -> Any q schema
mapAnyAny f v@(Here _) = Here $ f v
mapAnyAny f (There x) = There $ mapAnyAny (\y => f $ There y) x

mapAnyDep : {0 schema : Schema} ->
  (pos : Any p schema) -> (p pos.field -> q pos.field) -> Any q schema
mapAnyDep (Here  v) f = Here $ f v
mapAnyDep (There x) f = There $ mapAnyDep x f

makeAny : {0 schema : Schema} -> {0 p, q : FieldSchema -> Type} ->
  (pos : Any p schema) -> q pos.field -> Any q schema
makeAny (Here y) x = Here x
makeAny (There y) x = There $ makeAny y x

anyFwd : Any (q . p) schema -> Any q $ schemaMap p schema

replaceAll : {0 schema : Schema} -> All p schema -> All (\fld => p fld = q fld) schema ->
  All q schema
replaceAll rec prf = mapAnyAll
  (\z => Builtin.replace {p = id} (prf !! z) z.val)
  rec

replaceAny : {0 schema : Schema} -> {0 p,q : FieldSchema -> Type}-> (pos : Any p schema) ->
  (p pos.field === q pos.field) -> Any q schema
replaceAny pos prf = mapAnyDep pos (\v => replace {p = id} prf v)

recordMapAll : Record (schemaMap p schema) -> All ((.Sort) . p) schema
recordMapAll rec = allBwd' $ recordAll rec

Filter : (schema1, schema2 : Schema) -> Type
Filter schema1 schema2 = Any (\fld1 => Any (\fld2 => fld1.Sort -> fld2.Sort -> Bool) schema2) schema1

basicFilter : Record schema1 -> Record schema2 ->
  Filter schema1 schema2
  -> Bool
basicFilter rec1 rec2 filter =
  filter.val.val
    (recordAll rec1 !! filter)
    (recordAll rec2 !! filter.val)

filterRecord : Record schema1 -> Record schema2 ->
  List (Filter schema1 schema2)
  -> Bool
filterRecord rec1 rec2 filters = Prelude.all (basicFilter rec1 rec2) filters

(.missing) : Schema -> Schema
(.missing) = mapSchema Maybe

-- This is promising!
-- TODO: generalise to more general operations on Maybe
(.keepMissing) : Filter schema1 schema2 -> Filter (schema1.missing) (schema2.missing)
filter.keepMissing =
  let filterm : Maybe filter.field.Sort -> Maybe filter.val.field.Sort -> Bool
      filterm Nothing my = True
      filterm (Just x) Nothing = True
      filterm (Just x) (Just y) = filter.val.val x y
  in anyFwd $ makeAny filter $ anyFwd $ makeAny filter.val filterm

RecordFilter : (schema1, schema2 : Schema) -> Type
RecordFilter schema1 schema2 = Record schema1 -> Record schema2 -> Type

-- Subtle! We **have** to use a more intentional notion of equality,
-- since we don't want to succeed if the record has a missing value,
-- only if the value we're inspecting is missing.
(.missingRecord) : RecordFilter schema1 schema2 ->
  RecordFilter schema1.missing schema2.missing
recFilter.missingRecord rec1 rec2
  = let a1 = recordMapAll rec1
        a2 = recordMapAll rec2
    in  ?h1


{-

-- One more go
mapAll : {0 schema : Schema} -> (h : forall fld . f fld -> g fld) -> All f schema -> All g schema
mapAll h [<] = [<]
mapAll h (x :< y) = mapAll h x :< h y

blah : {schema : Schema} -> Not (schema = [<]) -> IsSnoc schema
blah {schema = [<]} f = absurd $ f Refl
blah {schema = (schema :< fs)} f = ItIsSnoc

blahblah : {schema : Schema} -> mapSchema f schema = [<] -> schema = [<]
blahblah {schema = [<]} Refl = Refl
blahblah {schema = _ :< _} Refl impossible

blah' : (schema = [<]) -> mapSchema f schema = [<]
blah' Refl = Refl

contraChain : (a -> b) -> Not b -> Not a
contraChain f g = g . f

blah'' : Not (mapSchema f schema = [<]) -> Not (schema = [<])
blah'' = contraChain blah'
{-
-- I think this might be the way to go
-- Another complicated identity function :)
gnu : Record a -> {auto 0 ford : a = mapSchema f schema} -> All (\fld => f fld.Sort) schema
gnu [<] with 0 (blahblah $ sym ford)
 gnu [<] | Refl = [<]
gnu (rec :< x) with 0 (blah $ blah'' $ \prf => case (trans ford prf) of _ impossible)
 gnu (rec :< x) | ItIsSnoc with 0 (ford)
  gnu (rec :< x) | ItIsSnoc | Refl = gnu rec {ford = Refl} :< x

convert : (f : Type -> Type) -> Record (mapSchema f schema) -> All (\fld => f fld.Sort) schema
convert f rec = gnu rec {ford = Refl}


-- Lets reinvent relational algebra

-- Am I going to regret publicly exporting these?

public export
record ProjectionJoin (src1, src2, tgt1, tgt2 : Schema) where
  constructor MkJoin
  0 filterSchema : Schema
  eqSchema : Eq (Record filterSchema)
  filter1 : Subst filterSchema src1
  filter2 : Subst filterSchema src2
  projection1 : Subst tgt1 src1
  projection2 : Subst tgt2 src2

public export
joinGen : ProjectionJoin src1 src2 tgt1 tgt2 -> Record src1 -> Record src2 -> Table (tgt1 ++ tgt2)
joinGen joinData rec1 rec2 =
  if (rec1.project (joinData.filter1) == rec2.project (joinData.filter2)) @{joinData.eqSchema}
  then [< rec1.project joinData.projection1 ++
          rec2.project joinData.projection2]
  else [<]

-- Using Any might be better

data SchemaLength : Nat -> Schema -> Type where
  Z : SchemaLength 0 [<]
  S : SchemaLength n schema -> SchemaLength (S n) (schema :< (h :! fld))

recallSchemaLength : (r : Record schema) -> Exists $ \n => SchemaLength n schema
recallSchemaLength [<] = Evidence 0 Z
recallSchemaLength (rec :< x) = let Evidence foo bar = recallSchemaLength rec in
  Evidence (S foo) (S bar)

public export
mapSchemaLength : {0 f : Type -> Type} ->
  (schema : Schema) ->
  ( Exists $ \n =>
  ( SchemaLength n schema
  , SchemaLength n (mapSchema f schema)
  ))
mapSchemaLength [<] = Evidence 0 (Z, Z)
mapSchemaLength (schema :< fs) with (mapSchemaLength {f} schema)
 mapSchemaLength (schema :< (h :! fs)) | (Evidence n (f1, f2)) = Evidence (S n) (S f1, S f2)

injectiveSchemaLength :
  (length1 : SchemaLength n1 schema) ->
  (length2 : SchemaLength n2 schema) ->
  n1 = n2
injectiveSchemaLength Z Z = Refl
injectiveSchemaLength (S x) (S y) = cong S (injectiveSchemaLength x y)

tabulateSchema : (n : Nat) -> (f : Fin n -> FieldSchema) -> Schema
tabulateSchema 0 f = [<]
tabulateSchema (S k) f = tabulateSchema k (f . FS) :< (f FZ)

data SchemaViewLin
  : (rec1, rec2, rec3 : Schema) -> Type where
  AllLin'  : SchemaViewLin [<] [<] [<]

data SchemaViewSnoc
  : (rec1, rec2, rec3 : Schema) -> Type where
  AllSnoc' : SchemaViewSnoc
    (schema1 :< (n1 :! fld1))
    (schema2 :< (n2 :! fld2))
    (schema3 :< (n3 :! fld3))

-- data SchemaLength : Nat -> Schema -> Type where
--  Z : SchemaLength 0 [<]
--  S : SchemaLength n schema -> SchemaLength (S n) (schema :< (h :! fld))

data SchemaLengthS : (SchemaLength n rec) -> Type where
  IsS : SchemaLengthS (S n)

data SchemaSnoc : Schema -> Type where
  IsSnoc : SchemaSnoc (schema :< (col :! type))

viewLen : (len : SchemaLength n (schema :< a)) -> SchemaLengthS len
viewLen (S _) = IsS

viewLenN : (len : SchemaLength (S n) schema) -> SchemaLengthS len
viewLenN (S _) = IsS

data SchemaBy : (xs, ys : Schema) -> Type where
  SZ : SchemaBy [<] [<]
  SS : SchemaBy schema schema' -> SchemaBy (schema :< fs) (schema' :< fs')

mapSchemaBy : (schema : Schema) -> (f : Type -> Type) -> SchemaBy schema (mapSchema f schema)
mapSchemaBy [<] f = SZ
mapSchemaBy (schema :< fs) f = SS (mapSchemaBy schema f)

recallSchemaLengthS : (0 isS : SchemaLengthS len) -> SchemaLengthS len
recallSchemaLengthS IsS = IsS


foo1 : {schema : Schema} -> Field (mapSchema f schema) x y -> Type
foo1 {schema = [<]} fld impossible
foo1 {schema = schema :< fs} Here = fs.Sort
foo1 {schema = schema :< fs} (There fld) = foo1 fld

foo2 : (fld : Field (mapSchema f schema) x y) ->
  Field schema x (foo1 {f,schema} fld)


mapValue :
  {0 f : Type -> Type} -> {c : forall a. a -> f a} ->
  (fld : Field (mapSchema f schema) x y) ->
  (rec : Record $ mapSchema f schema) -> y
mapValue fld rec = ?mapValue_rhs



zipperSchemaGen :
  (schema1, schema2, schema3 : Schema) ->
  {auto 0 length1 : SchemaLength n schema1} ->
  {auto 0 length2 : SchemaLength n schema2} ->
  {auto 0 length3 : SchemaLength n schema3} ->
  (combiner : (a,b,c : FieldSchema) -> FieldSchema) ->
  Schema
zipperSchemaGen  [<] schema2 schema3 combiner = [<]
zipperSchemaGen  (schema1 :< c1@(n1 :! fld1)) schema2 schema3
  {length1, length2, length3} combiner with 0 (viewLen length1)
  zipperSchemaGen
    (schema1 :< c1@(n1 :! fld1))
    (schema2 :< c2@(n2 :! fld2))
    (schema3 :< c3@(n3 :! fld3))
    {length1 = S length1, length2, length3} combiner | IsS with 0 (viewLen length2) | 0 (viewLen length3)
   zipperSchemaGen
    (schema1 :< c1@(n1 :! fld1))
    (schema2 :< c2@(n2 :! fld2))
    (schema3 :< c3@(n3 :! fld3))
    {length1 = S length1, length2 = S length2, length3 = S length3} combiner | IsS | IsS | IsS
    = zipperSchemaGen {length1, length2, length3} schema1 schema2 schema3 combiner :< combiner c1 c2 c3

zipperSchema :
  (schema1, schema2, schema3 : Schema) ->
  {auto 0 length1 : SchemaLength n schema1} ->
  {auto 0 length2 : SchemaLength n schema2} ->
  {auto 0 length3 : SchemaLength n schema3} ->
  Schema
zipperSchema schema1 schema2 schema3 =
  zipperSchemaGen schema1 schema2 schema3 {length1,length2,length3}
  $ \fld1,fld2,fld3 =>
    "\{fld1.Name} -> \{fld2.Name} -> \{fld3.Name}"
    :! (fld1.Sort -> fld2.Sort -> fld3.Sort)

zippedSchema :
  (schema1, schema2, schema3 : Schema) ->
  {auto 0 length1 : SchemaLength n schema1} ->
  {auto 0 length2 : SchemaLength n schema2} ->
  {auto 0 length3 : SchemaLength n schema3} ->
  Schema
zippedSchema schema1 schema2 schema3
  = zipperSchemaGen schema1 schema2 schema3 {length1,length2,length3}
  $ \_,_,fld3 => fld3

public export
zipWithRec :
  {auto 0 length1 : SchemaLength n schema1} ->
  {auto 0 length2 : SchemaLength n schema2} ->
  {auto 0 length3 : SchemaLength n schema3} ->
  (rec1 : Record schema1) ->
  (rec2 : Record schema2) ->
  (zipper : Record (zipperSchema schema1 schema2 schema3
                    {length1,length2,length3})) ->
  Record (zippedSchema schema1 schema2 schema3 {length1,length2,length3})
zipWithRec [<] rec2 zipper = [<]
zipWithRec (rec1 :< fld1) rec2 zipper
  {length1, length2, length3, schema3}
  with 0 (viewLen length1)
 zipWithRec (rec1 :< fld1) (rec2 :< fld2) zipper
  { length1 = S length1
  , length2
  , length3
  , schema3} | IsS with 0 (viewLenN length2) | 0 (viewLenN length3)
  zipWithRec (rec1 :< fld1) (rec2 :< fld2) zipper
    { length1 = S length1
    , length2 = S length2
    , length3 = S length3
    , schema3 = schema3 :< (n3 :! type3)} | IsS | IsS | IsS
    = let (zipper' :< zip) = zipper
      in zipWithRec rec1 rec2 zipper' :< zip fld1 fld2

reflexiveSchemaLength : (schema : Schema) -> SchemaLength (length schema) schema
reflexiveSchemaLength [<] = Z
reflexiveSchemaLength (schema :< (_ :! _)) = S (reflexiveSchemaLength schema)

mapSchemaLengthsAux : {schema : Schema} -> (schemaLength : SchemaLength n schema) -> (fs : List (Type -> Type)) ->
  All (\f => SchemaLength n (mapSchema f schema)) fs
mapSchemaLengthsAux _ [] = []
mapSchemaLengthsAux sL (f :: fs) =
  let sLength = mapSchemaLength {f} schema
      0 n = sLength.fst
      schemaLen = fst $ sLength.snd
      mapLen    = snd $ sLength.snd
      0 (Refl) = injectiveSchemaLength schemaLen sL
  in mapLen :: mapSchemaLengthsAux sL fs

mapSchemaLengths : {schema : Schema} -> (fs : List (Type -> Type)) ->
  All (\f => SchemaLength (length schema) (mapSchema f schema)) fs
mapSchemaLengths = mapSchemaLengthsAux (reflexiveSchemaLength schema)

public export
zipWithRecord : {0 f,g,h : Type -> Type} ->
  (c1 : forall a. a -> f a) ->
  (c2 : forall a. a -> g a) ->
  (d  : forall a. a -> h a) ->
  (zipper : forall a. f a -> g a -> h a) ->
  Record (mapSchema f schema) ->
  Record (mapSchema g schema) ->
  Record (mapSchema h schema)
zipWithRecord c1 c2 d zipper rec1 rec2 with 0 (mapSchemaLengths {schema} [f,g,h])
 zipWithRecord c1 c2 d zipper rec1 rec2 | xyz =
   let 0 length1 = indexAll                Here  xyz
       0 length2 = indexAll (There         Here) xyz
       0 length3 = indexAll (There $ There Here) xyz
   in let result = zipWithRec rec1 rec2 ?h190910
            {length1,length2,length3}
      in ?nearlythere

--mapRecord c [<] = [<]
--mapRecord c (rec :< fld) = mapRecord c rec :< c fld

public export
replicateRecord : {schema : Schema} -> {0 f : Type -> Type} -> (tab : forall a. f a) ->
  Record (mapSchema f schema)
replicateRecord {schema = [<]         } tab = [<]
replicateRecord {schema = schema :< fs} tab = replicateRecord tab :< tab

public export
joinGenMaybe : {tgt2 : Schema} ->
  ProjectionJoin src1 src2 tgt1 tgt2 -> Record src1 -> Record src2 ->
  Table (tgt1 ++ mapSchema Maybe tgt2)
joinGenMaybe joinData rec1 rec2 =
  [< rec1.project joinData.projection1 ++
  if (rec1.project (joinData.filter1) == rec2.project (joinData.filter2)) @{joinData.eqSchema}
  then mapRecord Just $ rec2.project joinData.projection2
  else replicateRecord Nothing
  ]


public export
0 jointSchemaType : (schema1, schema2 : Schema) -> String -> Type
jointSchemaType schema1 schema2 fld =
 Exists $ \type => ( Field schema1 fld type
                   , Field schema2 fld type
                   , Eq type
                   )
-- For now, since Data.List's intersect is export non-public

public export
jointNames : (schema1, schema2 : Schema) -> SnocList String
jointNames schema1 schema2 = (names schema1) `intersect` (names schema2)


-- TODO: should probably go into Data.Table.Schema.Renaming
embedSubtraction : {schema : Schema} -> {names : SnocList String} ->
  Subst (schema |-| names) schema
embedSubtraction {schema = [<]} = [<]
embedSubtraction  {schema = schema :< fs} {names} with (fs.Name `elem` names)
 _ | True = Schema.Quantifiers.map
              (\x => Evidence x.fst $ weakenField [<fs] x.snd)
              (embedSubtraction {schema})
 embedSubtraction {schema = schema :< fs@(_ :! _)} {names}
   | False = Schema.Quantifiers.map
                   (\x => Evidence x.fst $ weakenField [<fs] x.snd)
                   (embedSubtraction {schema})
             :< Evidence fs.Name Here



public export
equijoinData : (schema1, schema2 : Schema) -> (selection : SnocList String) -> Type
equijoinData schema1 schema2 selection = All (jointSchemaType schema1 schema2) selection

-- Extract the joinGen parameter out-of an equijoinData
public export
generateJoinData : {schema1,schema2 : Schema} ->
  (jointNames : SnocList String) ->
  equijoinData schema1 schema2 jointNames ->
  ProjectionJoin schema1 schema2 schema1 (schema2 |-| names schema1)

-- To implement it, we'll first define some auxiliary lemmata
-- to extract each field in `ProjectionJoin`.

total 0
fromAllSchema : {0 ns : SnocList String} -> {schema1 : Schema} ->
  equijoinData schema1 schema2 ns -> Schema
fromAllSchema [<] = [<]
fromAllSchema (joints :< joint) =
  fromAllSchema joints :<
  (last ns) :! joint.fst

Filter1 : {0 ns : SnocList String} -> {schema1 : Schema} ->
  (prf : equijoinData schema1 schema2 ns) ->
  Subst (fromAllSchema {schema1,schema2} prf) schema1
Filter1 [<] = [<]
Filter1 ((joints :< Evidence type (fld, _)) {x = name})
  =
  Filter1 joints :< Evidence name fld

Filter2 : {0 ns : SnocList String} -> {schema1 : Schema} ->
  (prf : equijoinData schema1 schema2 ns) ->
  Subst (fromAllSchema {schema1,schema2} prf) schema2
Filter2 [<] = [<]
Filter2 ((joints :< Evidence type (_, fld, _)) {x = name})
  = Filter2 joints :< Evidence _ fld

[emptyRecEq] Eq (Record [<]) where
  x == y = True

recordEq : All (\fld => Eq fld.Sort) schema -> Eq (Record schema)
recordEq [<] = emptyRecEq
recordEq {schema = schema :< (name :! type)} (eqs :< eq) =
   instance
   where
     recEq : ?
     recEq = recordEq eqs
     [instance] Eq (Record (schema :< (name :! type))) where
       (xs :< x) == (ys :< y) = (x == y) && (xs == ys) @{recEq}

mapSnocSchema : (prf : equijoinData schema1 schema2 ns) ->
  All (\fld => Eq fld.Sort) (fromAllSchema {schema1, schema2} prf)
mapSnocSchema [<] = [<]
mapSnocSchema (prfs :< prf) = mapSnocSchema prfs :< (snd $ snd $ prf.snd)

-- We can now put these together:
generateJoinData jointNames datum =
 MkJoin
   { eqSchema = recordEq (mapSnocSchema datum)
   , filter1 = Filter1 datum
   , filter2 = Filter2 datum
   , filterSchema = fromAllSchema datum
   , projection1 = IdSubst
   , projection2 = embedSubtraction
   }


public export
joinWhen : (t1 : Table schema1) -> (t2 : Table schema2) ->
  (keep : Record schema1 -> Record schema2 -> Bool) ->
  (combine : Record schema1 -> Record schema2 -> Record schema3) -> Table schema3
joinWhen t1 t2 keep combine = do
  x1 <- t1
  x2 <- t2
  ifThenElse (keep x1 x2)
    [< combine x1 x2]
    [< ]

public export
groupJoinWhen : (t1 : Table schema1) -> (t2 : Table schema2) ->
  (keep : Record schema1 -> Record schema2 -> Bool) ->
  (aggregate : Record schema1 -> Table schema2  -> Table schema3) -> Table schema3
groupJoinWhen t1 t2 keep aggregate = do
  x1 <- t1
  aggregate x1 (filter (keep x1) t2)


public export
joinWhenMissing : (t1 : Table schema1) -> (t2 : Table schema2) ->
  (keep : Record schema1 -> Record schema2 -> Bool) ->
  (combine : Record schema1 -> Maybe (Record schema2) -> Record schema3) -> Table schema3
joinWhenMissing t1 t2 keep combine =
    groupJoinWhen t1 t2 keep $
    \r1 => \case
      [<] => [< combine r1 Nothing]
      rs2 => map (combine r1 . Just) rs2

public export
join : Eq key => (t1 : Table schema1) -> (t2 : Table schema2) ->
  (getKey1 : Record schema1 -> key) -> (getKey2 : Record schema2 -> key) ->
  (combine : Record schema1 -> Record schema2 -> Record schema3) -> Table schema3
join t1 t2 getKey1 getKey2 combine =
  joinWhen t1 t2 (\r1, r2 => getKey1 r1 == getKey2 r2) combine

public export
groupJoin : Eq key => (t1 : Table schema1) -> (t2 : Table schema2) ->
  (getKey1 : Record schema1 -> key) ->
  (getKey2 : Record schema2 -> key) ->
  (aggregate : Record schema1 -> Table schema2 -> Record schema3) ->
  Table schema3
groupJoin t1 t2 getKey1 getKey2 aggregate =
  groupJoinWhen t1 t2 (\r1, r2 => getKey1 r1 == getKey2 r2)
  $ \r1,rs2 => [< aggregate r1 rs2]

public export
joinRecord : {schema1,schema2 : Schema}
  -> (rec1 : Record schema1) -> (rec2 : Record schema2)
  -> (jointNames : SnocList String)
  -> {auto 0 ford1 : u === (jointSchemaType schema1 schema2)}
  -> {auto joint : All u jointNames}
  -> Table (schema1 ++ (schema2 |-| names schema1))
joinRecord rec1 rec2 jointNames {joint, ford1 = Refl}
  = joinGen (generateJoinData jointNames joint) rec1 rec2

joinRecordMaybe : {schema1,schema2 : Schema}
  -> (rec1 : Record schema1) -> (rec2 : Record schema2)
  -> (jointNames : SnocList String)
  -> {auto 0 ford1 : u === (jointSchemaType schema1 schema2)}
  -> {auto joint : All u jointNames}
  -> Table (schema1 ++ mapSchema Maybe (schema2 |-| names schema1))
joinRecordMaybe rec1 rec2 jointNames {joint, ford1 = Refl}
  = joinGenMaybe (generateJoinData jointNames joint) rec1 rec2

public export
leftJoin : {schema1,schema2 : Schema}
  -> (tbl1 : Table schema1) -> (tbl2 : Table schema2)
  -> (jointNames : SnocList String)
  -> {auto 0 ford1 : u === (jointSchemaType schema1 schema2)}
  -> {auto joint : All u jointNames}
  -> Table (schema1 ++ (schema2 |-| names schema1))
leftJoin tbl1 tbl2 jointNames {ford1 = Refl} =
  let jointData = (generateJoinData jointNames joint)
  in join @{jointData.eqSchema} tbl1 tbl2
       (\r1 => r1.project jointData.filter1)
       (\r2 => r2.project jointData.filter2)
       (\r1, r2 => r1.project jointData.projection1 ++ r2.project jointData.projection2)


allSatisfy : {0 xs : SnocList a} -> (forall x. p x -> Bool) -> All p xs -> Bool
allSatisfy f [<] = True
allSatisfy f (ws :< w) = f w && allSatisfy f ws

public export
leftJoinMissing : {schema1,schema2,schema2' : Schema}
  -> (tbl1 : Table schema1) -> (tbl2 : Table schema2)
  -> (jointNames : SnocList String)
  -> {auto 0 ford1 : u === (jointSchemaType schema1 schema2)}
  -> {auto 0 ford2 : schema2 = mapSchema Maybe schema2'}
  -> {auto joint : All u jointNames}
  -> Table (schema1 ++ (mapSchema Maybe $ schema2' |-| names schema1))
leftJoinMissing tbl1 tbl2 jointNames {ford1 = Refl} {ford2 = Refl} =
  let jointData = (generateJoinData jointNames joint)
      _ = jointData.eqSchema
  in joinWhenMissing tbl1 tbl2
       (\r1,rm2 =>
            let rm2' = gnu rm2 {ford = Refl}
            in ?h1980
           {- all zipWith
           maybe True (\r2 =>
           r1.project jointData.filter1 ==
           r2.project jointData.filter2)
           mr2-})
       (\r1, mr2 => (r1.project jointData.projection1) ++
           (maybe
             (replicateRecord Nothing)
             (\r2 => mapRecord Just $ ?h1909) --r2.project jointData.projection2)
             mr2))

||| Hint so that `auto`-search can find appropriate `Exists`
||| instances. Don't export more generically as may cause unexpected
||| behaviour with other `Exists` instances.
%hint
public export
evidenceFieldNamed : (flds : (Field schema1 name type, Field schema2 name type, Eq type)) ->
  jointSchemaType schema1 schema2 name
evidenceFieldNamed {type} flds = Evidence type flds
-}
