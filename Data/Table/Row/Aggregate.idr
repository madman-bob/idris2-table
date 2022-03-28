module Data.Table.Row.Aggregate

import public Data.SortedMap

import public Data.Table.Data
import public Data.Table.Row.Constructor
import public Data.Table.Row.Interface

%default total

export
groupByFold : Ord k
           => (Record schema -> k)
           -> (Record schema -> v -> v)
           -> v
           -> Table schema
           -> SortedMap k v
groupByFold key f initial tbl = go tbl empty
  where
    update : Record schema -> SortedMap k v -> SortedMap k v
    update rec vs =
        let key = key rec in
        insert key (f rec $ maybe initial id $ lookup key vs) vs

    go : Table schema -> SortedMap k v -> SortedMap k v
    go [<] acc = acc
    go (tbl :< rec) acc = go tbl (update rec acc)

export
groupBy : Ord k
       => (Record schema -> k)
       -> (Record schema -> v)
       -> Table schema
       -> SortedMap k (List v)
groupBy key val tbl = groupByFold key ((::) . val) [] tbl

export
group : Ord a
     => (keyFld : Field schema keyCol a)
     -> Table schema
     -> SortedMap a (Table (drop schema keyFld))
group keyFld tbl = map mkTable $ groupBy (value keyFld) (dropField keyFld) tbl

export
groupMany : AllTypes Ord subschema
         => (ss : Subschema subschema schema)
         -> Table schema
         -> SortedMap (Record subschema) (Table (complement schema ss))
groupMany keyFld tbl = map mkTable $ groupBy (selectFields keyFld) (dropFields keyFld) tbl

export
groupKeepKey : Ord a
            => Field schema keyCol a
            -> Table schema
            -> SortedMap a (Table schema)
groupKeepKey keyFld tbl = map mkTable $ groupBy (value keyFld) id tbl

export
groupManyKeepKeys : AllTypes Ord subschema
                 => (ss : Subschema subschema schema)
                 -> Table schema
                 -> SortedMap (Record subschema) (Table schema)
groupManyKeepKeys keyFld tbl = map mkTable $ groupBy (selectFields keyFld) id tbl

export
countBy : Ord k
       => (Record schema -> k)
       -> Table schema
       -> SortedMap k Nat
countBy f = groupByFold f (const S) 0

export
count : Ord a
     => Field schema name a
     -> Table schema
     -> SortedMap a Nat
count fld = countBy (value fld)

infix 0 $$=

public export
data FieldAggregation : FieldSchema -> Type where
    ($$=) : (0 rename : RenameFieldSchema (oldName :! oldType)) -> (List oldType -> newType) -> FieldAggregation (oldName :! oldType)

public export
Aggregation : Schema -> Type
Aggregation schema = Many FieldAggregation schema

public export
0
aggSchema : Aggregation schema -> Schema
aggSchema [<] = [<]
aggSchema ((aggs :< agg) @{c}) = case c of
    ConcatLin =>
        let (_ ~> newName $$= _ ) {newType} = agg in
        aggSchema aggs :< (newName :! newType)
    ConcatSnoc d => aggSchema ((aggs :< agg) @{d})

public export
0
aggOldSchema : Aggregation schema -> Schema
aggOldSchema [<] = [<]
aggOldSchema ((aggs :< agg) @{c}) = case c of
    ConcatLin =>
        let (oldName ~> _ $$= _ ) {oldType} = agg in
        aggOldSchema aggs :< (oldName :! oldType)
    ConcatSnoc d => aggOldSchema ((aggs :< agg) @{d})

public export
aggFields : (aggs : Aggregation schema)
         -> Record schema
         -> Record (aggOldSchema aggs)
aggFields [<] rec = [<]
aggFields ((aggs :< (_ ~> _ $$= _)) @{ConcatLin}) (rec :< x) = aggFields aggs rec :< x
aggFields ((aggs :< agg) @{ConcatSnoc d}) (rec :< _) = aggFields ((aggs :< agg) @{d}) rec

empties : (aggs : Aggregation schema) => AllTypes List (aggOldSchema aggs)
empties @{[<]} = [<]
empties @{(aggs :< (_ ~> _ $$= _)) @{ConcatLin}} = empties @{aggs} :< TheTypeHas []
empties {schema = _ :< (_ :! _)} @{(aggs :< agg) @{ConcatSnoc d}} = empties @{(aggs :< agg) @{d}}

(::) : Record schema -> AllTypes List schema -> AllTypes List schema
[<] :: [<] = [<]
(rec :< x) :: (rest :< TheTypeHas col) = (rec :: rest) :< TheTypeHas (x :: col)

export
aggregationColumns : (aggs : Aggregation schema)
                  -> Table schema
                  -> AllTypes List (aggOldSchema aggs)
aggregationColumns aggs tbl = foldr (::) (empties @{aggs}) (map (aggFields aggs) tbl)

export
aggregateColumns : (aggs : Aggregation schema)
                -> AllTypes List (aggOldSchema aggs)
                -> Record (aggSchema aggs)
aggregateColumns [<] [<] = [<]
aggregateColumns ((aggs :< (_ ~> _ $$= f)) @{ConcatLin}) (cols :< TheTypeHas col) = aggregateColumns aggs cols :< f col
aggregateColumns {schema = _ :< (_ :! _)} ((aggs :< agg) @{ConcatSnoc c}) x = aggregateColumns ((aggs :< agg) @{c}) x

export
aggregate : (aggs : Aggregation schema)
         -> Table schema
         -> Record (aggSchema aggs)
aggregate aggs tbl = aggregateColumns aggs (aggregationColumns aggs tbl)

export
pivot : AllTypes Ord subschema
     => (ss : Subschema subschema schema)
     -> (aggs : Aggregation (complement schema ss))
     -> Table schema
     -> Table (subschema ++ aggSchema aggs)
pivot ss aggs tbl =
    mkTable $
    map (uncurry (++)) $
    SortedMap.toList $
    map (aggregate aggs) $
    groupMany ss tbl
