module Data.Table.Schema.Quantifiers

import Data.Table.Schema.Data

namespace All
  public export
  data All : (0 p : FieldSchema -> Type) -> Schema -> Type where
    Lin  : All p [<]
    (:<) : {0 schema : Schema} -> All p schema -> p col -> All p (schema :< col)

public export
length : All p schema -> Nat
length [<] = 0
length (all :< _) = S (length all)

public export
lengthAllLengthSchema : (all : All p schema) -> length all = length schema
lengthAllLengthSchema [<] = Refl
lengthAllLengthSchema (all :< _) = cong S (lengthAllLengthSchema all)
