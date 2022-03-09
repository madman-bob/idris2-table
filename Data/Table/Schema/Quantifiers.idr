module Data.Table.Schema.Quantifiers

import public Data.Table.Schema.Data

namespace All
    public export
    data All : (p : FieldSchema -> Type) -> Schema -> Type where
        Lin  : All p [<]
        (:<) : All p schema -> p col -> All p (schema :< col)

public export
length : All p schema -> Nat
length [<] = 0
length (all :< _) = S (length all)

public export
lengthAllLengthSchema : (all : All p schema) -> length all = length schema
lengthAllLengthSchema [<] = Refl
lengthAllLengthSchema (all :< _) = cong S (lengthAllLengthSchema all)

namespace AllTypes
    public export
    data TypeHas : (p : Type -> Type) -> FieldSchema -> Type where
        TheTypeHas : p type -> TypeHas p (name :! type)

    export
    here : (0 _ : TypeHas (=== ty) v) -> Field (schema :< v) (v .fieldName) ty
    here (TheTypeHas eq) = rewrite eq in Here

    public export
    AllTypes : (p : Type -> Type) -> Schema -> Type
    AllTypes p schema = All (TypeHas p) schema
