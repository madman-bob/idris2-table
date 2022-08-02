module Data.Table.Schema.Quantifiers

import public Data.Table.Schema.Data
import public Data.Table.Schema.Index

namespace All
    public export
    data All : (p : FieldSchema -> Type) -> Schema -> Type where
        Lin  : All p [<]
        (:<) : All p schema -> p col -> All p (schema :< col)


namespace Any
  public export
  data Any : (0 p : FieldSchema -> Type) -> Schema -> Type where
    Here  : p col -> Any p (schema :< col)
    There : Any p schema -> Any p (schema :< col)
public export
length : All p schema -> Nat
length [<] = 0
length (all :< _) = S (length all)

public export
lengthAllLengthSchema : (all : All p schema) -> length all = length schema
lengthAllLengthSchema [<] = Refl
lengthAllLengthSchema (all :< _) = cong S (lengthAllLengthSchema all)

public export
all : (forall x. (p x) -> Bool) ->  All p schema -> Bool
all f [<] = True
all f (xs :< x) = f x && all f xs

public export
modusPonens : All p schema -> Any q schema -> Any (\x => (p x, q x)) schema
modusPonens (all :< pWitness) (Here  qWitness) = Here (pWitness, qWitness)
modusPonens (all :< _       ) (There pos) = There (modusPonens all pos)

public export
map : (f : forall x. p x -> q x) -> All p schema -> All q schema
map f [<] = [<]
map f (all :< w) = map f all :< f w

public export
allFields : (schema : Schema) -> All (\fld => Field schema fld.Name fld.Sort) schema
allFields [<] = [<]
allFields (schema :< col@(_ :! _)) = map weaken (allFields schema) :< Here

public export
tab : {schema : Schema}
  -> (f : forall name, type. Field schema name type -> p (name :! type)) -> All p schema
tab {schema =        [<]   } f = [<]
tab {schema = schema :< (_ :! _)} f = tab (f . There) :< (f Here)

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

