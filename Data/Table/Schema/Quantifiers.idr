module Data.Table.Schema.Quantifiers

import public Data.Table.Schema.Data
import public Data.Table.Schema.Index

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

    public export
    AllTypes : (p : Type -> Type) -> Schema -> Type
    AllTypes p schema = All (TypeHas p) schema

namespace Initial
    public export
    data Initial : (xs : Schema)
                -> (init : Schema)
                -> Type where [uniqueSearch, search xs]
        WholeSchema : Initial xs xs
        InitialSchema : Initial xs init -> Initial (xs :< x) init

    %name Initial i, j

    public export
    fromString : (name : String)
              -> Initial schema (init :< (name :! type))
              => Initial schema (init :< (name :! type))
    fromString name @{i} = i

    public export
    data Take : (xs : Schema)
             -> (init : Schema)
             -> (n : Nat)
             -> Type where [uniqueSearch, search xs]
        TakeAll : HasLength xs n -> Take xs xs n
        SkipLast : Take xs init n -> Take (xs :< x) init n

    %name Take tk

    public export
    fromInteger : (index : Integer)
               -> Take schema init (S $ cast index)
               => Initial schema init
    fromInteger index @{TakeAll _} = WholeSchema
    fromInteger index @{SkipLast tk} = InitialSchema $ fromInteger index @{tk}

namespace Many
    public export
    data Many : (p : FieldSchema -> Type) -> (xs : Schema) -> Type where
        Lin : Many p xs
        (:<) : Many p init
            -> p x
            -> Initial xs (init :< x)
            => Many p xs

    %name Many pxs, pys, pzs
