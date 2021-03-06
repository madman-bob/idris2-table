module Data.Table.Row

import Data.List
import public Data.SnocList

import public Data.Table.Data
import public Data.Table.Row.Aggregate
import public Data.Table.Row.Constructor
import public Data.Table.Row.Frame
import public Data.Table.Row.HasRows
import public Data.Table.Row.Interface
import public Data.Table.Row.Quantifiers

%default total

public export
distinctBy : (Record schema -> Record schema -> Bool) -> Table schema -> Table schema
distinctBy f tbl = foldl (\acc, rec => ifThenElse (elemBy f rec acc) acc (acc :< rec)) [<] $ toSnocList tbl

public export
distinct : Eq (Record schema) => Table schema -> Table schema
distinct = distinctBy (==)

public export
enum : (tbl : Table schema)
    -> HasRows tbl n
    => SnocList (Fin n, Record schema)
enum tbl = snd $ enum' tbl
  where
    enum' : (t : Table schema)
         -> HasRows t m
         => (Fin (S m), SnocList (Fin m, Record schema))
    enum' [<] = (FZ, [<])
    enum' {m = S m} (t :< rec) @{SnocTable _} =
        let (k, acc) = enum' t in
        (FS k, Prelude.map (mapFst weaken) acc :< (k, rec))

public export
findIndexFromEndBy : (Record schema -> Bool)
                  -> (tbl : Table schema)
                  -> {auto 0 hasRows : HasRows tbl n}
                  -> Maybe (Fin n)
findIndexFromEndBy f [<] = Nothing
findIndexFromEndBy f (tbl :< rec) {hasRows = SnocTable _} =
    if f rec
        then Just FZ
        else FS <$> findIndexFromEndBy f tbl

public export
findIndexBy : (Record schema -> Bool)
           -> (tbl : Table schema)
           -> HasRows tbl n
           => Maybe (Fin n)
findIndexBy f tbl =
    let Val _ = length tbl in
    complement <$> findIndexFromEndBy f tbl

public export
findIndex : Eq (Record schema)
         => Record schema
         -> (tbl : Table schema)
         -> HasRows tbl n
         => Maybe (Fin n)
findIndex rec = findIndexBy (== rec)

export
sortBy : (Record schema -> Record schema -> Ordering) -> Table schema -> Table schema
sortBy cmp tbl = mkTable $ List.sortBy cmp (cast $ toSnocList tbl)

export
sort : Ord (Record schema) => Table schema -> Table schema
sort = sortBy compare

public export
filter : (Record schema -> Bool) -> Table schema -> Table schema
filter f tbl = do
    rec <- tbl
    case f rec of
        False => [<]
        True => pure rec

public export
dropNa : (fld : Field schema name (Maybe type))
      -> Table schema
      -> Table (update schema fld type)
dropNa fld tbl = do
    rec <- tbl
    case value fld rec of
        Nothing => [<]
        Just x => pure $ setField fld x rec

namespace Flatten
    public export
    data Flatten : (t : Type -> Type)
                -> (flatSchema : Schema)
                -> (tSchema : Schema)
                -> Type where [search t tSchema]
      Lin : Flatten t schema schema
      (:<) : Flatten t f s
          -> Concat flatSchema (f :< (name :! type)) rest
          -> Concat schema (s :< (name :! t type)) rest
          => Flatten t flatSchema schema

    unroll' : Applicative t
           => Zippable t
           => Foldable t
           => Flatten t flatSchema schema
           -> Record schema
           -> t (Record flatSchema)
    unroll' [<] rec = pure rec
    unroll' ((fltn :< ConcatLin) @{ConcatLin}) (rec :< x) = zipWith (:<) (unroll' fltn rec) x
    unroll' ((fltn :< ConcatSnoc c) @{ConcatSnoc _}) (rec :< x) = (:< x) <$> unroll' (fltn :< c) rec

    export
    unroll : Applicative t
          => Zippable t
          => Foldable t
          => Flatten t flatSchema schema
          -> Record schema
          -> Table flatSchema
    unroll fltn rec = mkTable $ unroll' fltn rec

    export
    flatten : Applicative t
           => Zippable t
           => Foldable t
           => Flatten t flatSchema schema
           -> Table schema
           -> Table flatSchema
    flatten f tbl = do
        rec <- tbl
        unroll f rec
