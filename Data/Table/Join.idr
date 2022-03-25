module Data.Table.Join

import public Data.Table.Column
import public Data.Table.Data
import public Data.Table.Record
import public Data.Table.Row
import public Data.Table.Row.Constructor
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
  equijoinData schema1 schema2 (jointNames schema1 schema2) ->
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
generateJoinData datum =
 MkJoin
   { eqSchema = recordEq (mapSnocSchema datum)
   , filter1 = Filter1 datum
   , filter2 = Filter2 datum
   , filterSchema = fromAllSchema datum
   , projection1 = IdSubst
   , projection2 = embedSubtraction
   }

public export
joinRecord : {schema1,schema2 : Schema} -> (rec1 : Record schema1) -> (rec2 : Record schema2)
  -> {auto 0 ford1 : u === (jointSchemaType schema1 schema2)}
  -> {auto 0 ford2 : v === (jointNames schema1 schema2)}
  -> {auto joint : All u v}
  -> Table (schema1 ++ (schema2 |-| names schema1))
joinRecord rec1 rec2 {joint, ford1 = Refl, ford2 = Refl} 
  = joinGen (generateJoinData joint) rec1 rec2

public export
join : {schema1,schema2 : Schema} -> (tbl1 : Table schema1) -> (tbl2 : Table schema2)
  -> {auto 0 ford1 : u === (jointSchemaType schema1 schema2)}
  -> {auto 0 ford2 : v === (jointNames schema1 schema2)}
  -> {auto joint : All u v}
  -> Table (schema1 ++ (schema2 |-| names schema1))
join tbl1 tbl2 {joint, ford1 = Refl, ford2 = Refl} = do
  row1 <- tbl1
  row2 <- tbl2
  joinRecord row1 row2


||| Hint so that `auto`-search can find appropriate `Exists`
||| instances. Don't export more generically as may cause unexpected
||| behaviour with other `Exists` instances.
%hint
public export
evidenceFieldNamed : (flds : (Field schema1 name type, Field schema2 name type, Eq type)) ->
  jointSchemaType schema1 schema2 name
evidenceFieldNamed {type} flds = Evidence type flds

-- TODO: create actual tests
S1, S2 : Schema
S1 = [< "a" :! Nat, "b" :! Bool, "c" :! String]
S2 = [< "a" :! Nat, "b" :! Bool, "d" :! Double]

T1 : Table S1
T1  =[< [<2, True , "hello"]
     ,  [<2, False, "hello"]
     ]
T2 : Table S2
T2 = [< [<2, True, 3.5]
     ,  [<2, True, 6.5]
     ]

H : ?
H = join T1 T2
