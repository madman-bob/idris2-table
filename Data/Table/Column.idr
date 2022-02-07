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
addColumn : (0 name : String)
         -> (col : SnocList type)
         -> (tbl : Table schema)
         -> {auto 0 nRows : HasRows tbl (length col)}
         -> Table (schema :< name :! type)
addColumn name [<] [<] {nRows = EmptyTable} = [<]
addColumn name (col :< x) (tbl :< rec) {nRows = SnocTable _} = addColumn name col tbl :< (rec :< x)

public export
buildColumn : (0 name : String)
           -> (Record schema -> type)
           -> Table schema
           -> Table (schema :< name :! type)
buildColumn name f tbl =
    let (_ ** _) = length tbl in
    addColumn name (map f tbl) tbl {nRows = mapPreservesLength}

public export
dropColumn : (fld : Field schema name type)
          -> Table schema
          -> Table (drop schema fld)
dropColumn fld tbl = mkTable $ map (dropField fld) tbl
