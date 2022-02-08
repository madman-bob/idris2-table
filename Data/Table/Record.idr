module Data.Table.Record

import public Data.Table.Schema

%default total

public export
data Record : Schema -> Type where
    Lin : Record [<]
    (:<) : Record schema -> type -> Record (schema :< (name, type))

%name Record rec

public export
value : Field schema name type
     -> Record schema
     -> type
value Here (rec :< x) = x
value (There fld) (rec :< x) = value fld rec

public export
dropField : (fld : Field schema name type)
         -> Record schema
         -> Record (drop schema fld)
dropField Here (rec :< x) = rec
dropField (There fld) (rec :< x) = dropField fld rec :< x

public export
Eq (Record [<]) where
    [<] == [<] = True

public export
Eq a => Eq (Record schema) => Eq (Record (schema :< (name, a))) where
    (r :< x) == (s :< y) = x == y && delay (r == s)

public export
Ord (Record [<]) where
    compare [<] [<] = EQ

public export
Ord a => Ord (Record schema) => Ord (Record (schema :< (name, a))) where
    compare (r :< x) (s :< y) = compare (r, x) (s, y)

public export
byField : Field schema name type
       -> Ord type
       => Eq (Record schema)
       => Ord (Record schema)
byField fld = ByField
  where
    [ByField] Ord (Record schema) where
        compare = compare `on` value fld

public export
(|+|) : Record schema1 -> Record schema2 -> Record (schema1 |+| schema2)
rec1 |+| [<] = rec1
rec1 |+| (rec2 :< fld) = (rec1 |+| rec2) :< fld
