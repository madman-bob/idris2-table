module Data.Table.Record

import public Data.Table.Schema

%default total

public export
data Record : Schema -> Type where
    Lin : Record [<]
    (:<) : Record schema -> type -> Record (schema :< (name :! type))

%name Record rec

public export
value : Field schema name type
     -> Record schema
     -> type
value Here (rec :< x) = x
value (There fld) (rec :< x) = value fld rec

public export
replaceField : (fld : Field schema name type)
            -> (0 newName : String)
            -> newType
            -> Record schema
            -> Record (replace schema fld (newName :! newType))
replaceField Here newName x (rec :< _) = rec :< x
replaceField (There fld) newName x (rec :< y) = replaceField fld newName x rec :< y

public export
setField : (fld : Field schema name type)
        -> newType
        -> Record schema
        -> Record (update schema fld newType)
setField Here x (rec :< _) = rec :< x
setField (There fld) x (rec :< y) = setField fld x rec :< y

public export
updateField : (fld : Field schema name type)
           -> (type -> newType)
           -> Record schema
           -> Record (update schema fld newType)
updateField fld f rec = setField fld (f $ value fld rec) rec

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
Eq a => Eq (Record schema) => Eq (Record (schema :< (name :! a))) where
    (r :< x) == (s :< y) = x == y && delay (r == s)

public export
Ord (Record [<]) where
    compare [<] [<] = EQ

public export
Ord a => Ord (Record schema) => Ord (Record (schema :< (name :! a))) where
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
