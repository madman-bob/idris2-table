module Data.Table.Schema.Quantifiers

import public Data.Table.Schema.Data

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
