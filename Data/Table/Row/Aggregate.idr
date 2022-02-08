module Data.Table.Row.Aggregate

import public Data.SortedMap

import public Data.Table.Data
import public Data.Table.Row.Constructor

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
groupKeepKey : Ord a
            => Field schema keyCol a
            -> Table schema
            -> SortedMap a (Table schema)
groupKeepKey keyFld tbl = map mkTable $ groupBy (value keyFld) id tbl

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
