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

namespace Concat
    public export
    data Concat : (xs : Schema)
               -> (init : Schema)
               -> (rest : Schema)
               -> Type where [uniqueSearch, search xs]
        ConcatLin : Concat xs xs [<]
        ConcatSnoc : Concat xs init rest -> Concat (xs :< x) init (rest :< x)

    %name Concat c, d

    public export
    fromString : (name : String)
              -> Concat schema (init :< (name :! type)) rest
              => Concat schema (init :< (name :! type)) rest
    fromString name @{c} = c

    public export
    data Take : (xs : Schema)
             -> (init : Schema)
             -> (rest : Schema)
             -> (n : Nat)
             -> Type where [uniqueSearch, search xs]
        TakeAll : HasLength xs n -> Take xs xs [<] n
        SkipLast : Take xs init rest n -> Take (xs :< x) init (rest :< x) n

    %name Take tk

    public export
    fromInteger : (index : Integer)
               -> Take schema init rest (S $ cast index)
               => Concat schema init rest
    fromInteger index @{TakeAll _} = ConcatLin
    fromInteger index @{SkipLast tk} = ConcatSnoc $ fromInteger index @{tk}

namespace Many
    public export
    data Many : (p : FieldSchema -> Type) -> (xs : Schema) -> Type where
        Lin : Many p xs
        (:<) : Many p init
            -> p x
            -> Concat xs (init :< x) rest
            => Many p xs

    %name Many pxs, pys, pzs
