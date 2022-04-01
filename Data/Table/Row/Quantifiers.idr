module Data.Table.Row.Quantifiers

import public Data.Table.Data

public export
data AllRows : (p : Record schema -> Type) -> Table schema -> Type where
    Lin : AllRows p [<]
    (:<) : AllRows p tbl -> p rec -> AllRows p (tbl :< rec)
