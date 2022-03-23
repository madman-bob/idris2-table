module Data.Table.Schema

import public Data.Table.Schema.Data
import public Data.Table.Schema.Index
import public Data.Table.Schema.Subschema
import public Data.Table.Schema.Quantifiers

%default total

public export
fromString : (name : String)
          -> {auto fld : Field schema name type}
          -> Field schema name type
fromString name = fld

public export
replace : (schema : Schema)
       -> Field schema name type
       -> FieldSchema
       -> Schema
replace (schema :< (name :! type)) Here newFS = schema :< newFS
replace (schema :< fs) (There fld) newFS = replace schema fld newFS :< fs

namespace RenameMany
    infix 10 ~>

    public export
    data RenameFieldSchema : FieldSchema -> Type where
        (~>) : (oldName : String) -> (newName : String) -> RenameFieldSchema (oldName :! type)

    public export
    RenameSchema : Schema -> Type
    RenameSchema schema = Many RenameFieldSchema schema

    public export
    rename : (schema : Schema)
          -> RenameSchema schema
          -> Schema
    rename schema [<] = schema
    rename o@(schema :< fs) ((renames :< rs) @{c}) with ()
      rename o@(schema :< (oldName :! type)) ((renames :< (oldName ~> newName)) @{ConcatLin}) | _ = rename schema renames :< (newName :! type)
      rename o@(schema :< fs) ((renames :< rs) @{ConcatSnoc _}) | _ = rename schema (renames :< rs) :< fs

public export
update : (schema : Schema)
      -> Field schema name type
      -> Type
      -> Schema
update (schema :< (name :! type)) Here newType = schema :< (name :! newType)
update (schema :< fs) (There fld) newType = update schema fld newType :< fs

namespace UpdateMany
    public export
    data UpdateFieldSchema : FieldSchema -> Type where
        (:!) : (name : String) -> (newType : Type) -> UpdateFieldSchema (name :! oldType)

    public export
    UpdateSchema : Schema -> Type
    UpdateSchema schema = Many UpdateFieldSchema schema

    public export
    update : (schema : Schema)
          -> UpdateSchema schema
          -> Schema
    update schema [<] = schema
    update o@(schema :< fs) ((updates :< us) @{c}) with ()
      update o@(schema :< (name :! oldType)) ((updates :< (name :! newType)) @{ConcatLin}) | _ = update schema updates :< (name :! newType)
      update o@(schema :< fs) ((updates :< us) @{ConcatSnoc _}) | _ = update schema (updates :< us) :< fs

public export
drop : (schema : Schema)
    -> Field schema name type
    -> Schema
drop (schema :< (name :! type)) Here = schema
drop (schema :< fs) (There fld) = drop schema fld :< fs
