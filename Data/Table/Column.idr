module Data.Table.Column

import public Data.SnocList

import public Data.Table.Column.Homogeneous
import public Data.Table.Data
import public Data.Table.Row

%default total

public export
column : Field schema name type
      -> Table schema
      -> SnocList type
column fld tbl = map (value fld) tbl

public export
selectColumns : Subschema subschema schema
             -> Table schema
             -> Table subschema
selectColumns ss = map (selectFields ss)

public export
addColumn : (0 name : String)
         -> (col : SnocList type)
         -> (tbl : Table schema)
         -> {auto 0 nRows : HasRows tbl (length col)}
         -> Table (schema :< name :! type)
addColumn name [<] [<] {nRows = EmptyTable} = [<]
addColumn name (col :< x) (tbl :< rec) {nRows = SnocTable _} = addColumn name col tbl :< (rec :< x)

public export
replaceColumn : (fld : Field schema name type)
             -> (0 newName : String)
             -> (type -> newType)
             -> Table schema
             -> Table (replace schema fld (newName :! newType))
replaceColumn fld newName f [<] = [<]
replaceColumn fld newName f (tbl :< rec) = replaceColumn fld newName f tbl :< replaceField fld newName (f $ value fld rec) rec

public export
updateColumn : (fld : Field schema name type)
            -> (type -> newType)
            -> Table schema
            -> Table (update schema fld newType)
updateColumn fld f [<] = [<]
updateColumn fld f (tbl :< rec) = updateColumn fld f tbl :< updateField fld f rec

public export
buildColumn : (0 name : String)
           -> (Record schema -> type)
           -> Table schema
           -> Table (schema :< name :! type)
buildColumn name f tbl =
    let (_ ** _) = length tbl in
    addColumn name (map f tbl) tbl {nRows = SnocList.mapPreservesLength}

public export
dropColumn : (fld : Field schema name type)
          -> Table schema
          -> Table (drop schema fld)
dropColumn fld tbl = mkTable $ map (dropField fld) tbl

public export
dropColumns : (ss : Subschema subschema schema)
           -> Table schema
           -> Table (complement schema ss)
dropColumns ss = map (dropFields ss)
