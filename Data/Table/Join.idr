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
import public Data.SnocList.Operations
import public Data.SnocList.Quantifiers
import public Data.List.Quantifiers

import Data.Table.Show

import Syntax.WithProof

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

public export
mapSchema : (Type -> Type) -> Schema -> Schema
mapSchema f [<] = [<]
mapSchema f (schema :< fs) = mapSchema f schema :< (fs.Name :! f fs.Sort)

public export
mapRecord : {0 f : Type -> Type} -> (c : forall a. a -> f a) -> Record schema ->
  Record (mapSchema f schema)
mapRecord c [<] = [<]
mapRecord c (rec :< fld) = mapRecord c rec :< c fld

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

tabulateSchema : (n : Nat) -> (f : Fin n -> FieldSchema) -> Schema
tabulateSchema 0 f = [<]
tabulateSchema (S k) f = tabulateSchema k (f . FS) :< (f FZ)

data SchemaView : (schema1, schema2 : Schema) -> Type where
  BothLin  : SchemaView [<] [<]
  BothSnoc : SchemaView (rec1 :< (n1 :! fld1)) (rec2 :< (n2 :! fld2))

data SchemaView'
  : (rec1, rec2, rec3 : Schema) -> Type where
  AllLin  : SchemaView' [<] [<] [<]
  AllSnoc : SchemaView' (schema1 :< (n1 :! fld1))
                        (schema2 :< (n2 :! fld2))
                        (schema3 :< (n3 :! fld3))



0 viewBoth :
  (schema1, schema2 : Schema) ->
  {auto length1 : SchemaLength n schema1} ->
  {auto length2 : SchemaLength n schema2} ->
  SchemaView schema1 schema2
viewBoth [<] rec2 =
  let (Z) = length1
      (Z) = length2
  in BothLin
viewBoth (rec :< (_ :! _)) rec2 =
  let (S k1) = length1
      (S k2) = length2
  in BothSnoc
{-
0 viewAll :
  (schema1, schema2, schema3 : Schema) ->
  {auto 0 length1 : SchemaLength n schema1} ->
  {auto 0 length2 : SchemaLength n schema2} ->
  {auto 0 length3 : SchemaLength n schema3} ->
  SchemaView' schema1 schema2 schema3
viewAll [<] rec2 rec3 =
  let (Z) = length1
      (Z) = length2
      (Z) = length3
  in AllLin
viewAll (rec :< x) rec2 rec3 =
  let (   S _) = length1
      (   S _) = length2
      (   S _) = length3
  in AllSnoc

zipperSchemaGen :
  (schema1, schema2, schema3 : Schema) ->
  {auto 0 length1 : SchemaLength n schema1} ->
  {auto 0 length2 : SchemaLength n schema2} ->
  {auto 0 length3 : SchemaLength n schema3} ->
  (combiner : (a,b,c : FieldSchema) -> FieldSchema) ->
  Schema
zipperSchemaGen  [<] schema2 schema3 combiner = [<]
zipperSchemaGen  (schema :< fs) schema2 schema3 combiner =
  case viewAll [<] schema2 schema3 {length1,length2,length3} of
    (AllSnoc {schema1, schema2, schema3, n1, n2, n3, fld1, fld2, fld3}) =>
        ?zipperSchemaGen_rhs_2

zipperSchemaGen [<] [<] [<] _
  { length1 = Z
  , length2 = Z
  , length3 = Z
  }
  = [<]
zipperSchemaGen [<] (_ :< _)  _ _
  { length1 = Z
  , length2 = _
  , length3 = _
  } impossible

zipperSchemaGen [<] _ (_ :< _) _
  { length1 = Z
  , length2 = _
  , length3 = _
  } impossible

zipperSchemaGen (schema1 :< fs1) (schema2 :< fs2) (schema3 :< fs3) combiner
  { length1 = S length1
  , length2 = S length2
  , length3 = S length3
  }
  = zipperSchemaGen schema1 schema2 schema3 {length1, length2, length3} combiner
  :< (combiner fs1 fs2 fs3)
-- Boilerplate, deal with missing cases
zipperSchemaGen (schema :< fs) [<] _ _
  { length1 = S n
  , length2 = _
  , length3 = _
  } impossible
zipperSchemaGen (schema :< fs) _ [<] _
  { length1 = S n
  , length2 = _
  , length3 = _
  } impossible

-- Disgusting. Generalise so that you only do this once
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


public export
zipWithRecord : {0 f,g,h : Type -> Type} ->
  (c1 : forall a. a -> f a) ->
  (c2 : forall a. a -> g a) ->
  (d  : forall a. a -> h a) ->
  (zipper : forall a. f a -> g a -> h a) ->
  Record (mapSchema f schema) ->
  Record (mapSchema g schema) ->
  Record (mapSchema h schema)
zipWithRecord c1 c2 d zipper rec rec1 with 0 (mapSchemaLength {f} schema) | (recallSchemaLength rec1)
 zipWithRecord c1 c2 d zipper rec rec1 | (Evidence n foo) | (Evidence m bar) = ?zipWithRecord_rhs_00
 zipWithRecord c1 c2 d zipper rec rec1 | (Evidence n foo) | (Evidence m bar) = ?zipWithRecord_rhs_0
--mapRecord c [<] = [<]
--mapRecord c (rec :< fld) = mapRecord c rec :< c fld
-}

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
       (\r1, mr2 =>
           ?h10
           {- all zipWith
           maybe True (\r2 =>
           r1.project jointData.filter1 ==
           r2.project jointData.filter2)
           mr2-})
       (\r1, mr2 => (r1.project jointData.projection1) ++
           (maybe
             (replicateRecord Nothing)
             (\r2 => mapRecord Just $ ?h190) --r2.project jointData.projection2)
             mr2))

||| Hint so that `auto`-search can find appropriate `Exists`
||| instances. Don't export more generically as may cause unexpected
||| behaviour with other `Exists` instances.
%hint
public export
evidenceFieldNamed : (flds : (Field schema1 name type, Field schema2 name type, Eq type)) ->
  jointSchemaType schema1 schema2 name
evidenceFieldNamed {type} flds = Evidence type flds
