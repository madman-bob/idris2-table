module Data.Table.Schema.Index

import public Data.Table.Schema.Data

%default total

public export
data HasLength : (schema : Schema) -> (n : Nat) -> Type where [search schema]
    EmptySchema : HasLength [<] 0
    SnocSchema : HasLength schema n -> HasLength (schema :< (name, type)) (S n)

%name HasLength lth

public export
data HasIndex : (schema : Schema)
             -> (fld : Field schema name type)
             -> (i : Nat)
             -> Type where [search schema i]
    LastIndex : HasLength (schema :< (name, type)) (S i) -> HasIndex (schema :< (name, type)) Here i
    PrevIndex : HasIndex schema fld i -> HasIndex (schema :< (n, t)) (There fld) i

%name HasIndex idx

public export
fromInteger : (0 x : Integer)
           -> {fld : Field schema name type}
           -> {auto 0 hasIndex : HasIndex schema fld (fromInteger x)}
           -> Field schema name type
fromInteger x = fld
