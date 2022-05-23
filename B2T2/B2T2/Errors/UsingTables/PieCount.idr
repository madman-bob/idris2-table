module B2T2.Errors.UsingTables.PieCount

import Data.Table

import B2T2.ExampleTables

count : Ord a
     => Field schema name a
     -> Table schema
     -> Table [<"value" :! a, "count" :! Nat]

data Image : Type where [external]

pieChart : Ord key
        => Field schema name1 key
        -> Field schema name2 Nat
        -> Table schema
        -> Image

failing "Can't find an implementation for Field"
    ||| Similarly to the midFinal example, the string literals
    ||| `"true"` and `"get acne"` fail to type-check, as Idris 2 proof
    ||| search fails to find columns of those names in the schema of
    ||| the table returned by `count`. So this example fails at
    ||| compile-time.
    img : Image
    img = pieChart "true" "get acne" $ count "get acne" jellyAnon

||| As both `"value"` and `"count"` *are* in the schema of the
||| table returned by `count`, and the types of these columns
||| satisfy the additional constraints required by `pieChart`,
||| this example type-checks successfully.
img : Image
img = pieChart "value" "count" $ count "get acne" jellyAnon
