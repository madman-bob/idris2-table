module Data.Table.Schema.Quantifiers

import Data.Table.Schema.Data

namespace All
  public export
  data All : (0 p : (String, Type) -> Type) -> Schema -> Type where
    Lin  : All p [<]
    (:<) : {0 schema : Schema} -> All p schema -> p col -> All p (schema :< col)
