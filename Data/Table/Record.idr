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
selectFields : Subschema subschema schema
            -> Record schema
            -> Record subschema
selectFields [<] rec = [<]
selectFields (ss :< WholeSchema) (rec :< x) = selectFields ss rec :< x
selectFields (ss :< InitialSchema i) (rec :< x) = selectFields (ss :< i) rec

public export
renameFields : (rs : RenameSchema schema)
            -> Record schema
            -> Record (rename schema rs)
renameFields [<] rec = rec
renameFields ((renames :< (_ ~> _)) @{WholeSchema}) (rec :< x) = renameFields renames rec :< x
renameFields ((renames :< (oldName ~> newName)) @{InitialSchema _}) (rec :< x) = renameFields (renames :< (oldName ~> newName)) rec :< x

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

namespace Update
    infix 10 ::=

    public export
    data UpdateField : UpdateFieldSchema fs -> Type where
        (::=) : (0 name : String) -> type -> UpdateField (name :! type)

    public export
    data Update : UpdateSchema schema -> Type where
        Lin : Update [<]
        (:<) : Update {schema = init} us
            -> UpdateField {fs} ufs
            -> (initPrf : Initial schema (init :< fs))
            => Update ((us :< ufs) @{initPrf})

    public export
    updateFields : Update {schema} us
                -> Record schema
                -> Record (update schema us)
    updateFields [<] rec = rec
    updateFields ((updates :< (_ ::= x)) @{WholeSchema}) (rec :< _) = updateFields updates rec :< x
    updateFields ((updates :< uf@(_ ::= _)) @{InitialSchema _}) (rec :< y) = updateFields (updates :< uf) rec :< y

public export
dropField : (fld : Field schema name type)
         -> Record schema
         -> Record (drop schema fld)
dropField Here (rec :< x) = rec
dropField (There fld) (rec :< x) = dropField fld rec :< x

public export
dropFields : (ss : Subschema subschema schema)
          -> Record schema
          -> Record (complement schema ss)
dropFields [<] rec = rec
dropFields (ss :< WholeSchema) (rec :< x) = dropFields ss rec
dropFields (ss :< InitialSchema i) (rec :< x) = dropFields (ss :< i) rec :< x

public export
(++) : Record schema1 -> Record schema2 -> Record (schema1 ++ schema2)
rec1 ++ [<] = rec1
rec1 ++ (rec2 :< x) = (rec1 ++ rec2) :< x

public export
AllTypes Eq schema => Eq (Record schema) where
    ([<] == [<]) @{[<]} = True
    ((r :< x) == (s :< y)) @{_ :< TheTypeHas _} = x == y && delay (r == s)

%hint
public export
allTypesOrdEq : AllTypes Ord schema => AllTypes Eq schema
allTypesOrdEq @{[<]} = [<]
allTypesOrdEq @{_ :< TheTypeHas _} = %search :< %search

public export
AllTypes Ord schema => Ord (Record schema) where
    compare [<] [<] = EQ
    compare @{_ :< TheTypeHas _} (r :< x) (s :< y) = compare (r, x) (s, y)

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
(.project) : (rec : Record schema) -> FieldTyped schema type -> type
rec.project pos = value pos.snd rec

