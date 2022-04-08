module B2T2.Errors.UsingTables.MidFinal

import Data.Table

import B2T2.ExampleTables

data Image : Type where [external]

scatterPlot : Field schema name1 Nat
           -> Field schema name2 Nat
           -> Table schema
           -> Image

failing "Can't find an implementation for Field"
    ||| A `Field schema name type` object is a constructive proof that
    ||| a field called `name` of type `type` exists in `schema`.
    |||
    ||| For convenience, we overload the Idris 2 string literal
    ||| notation to attempt to create a `Field` of that name.
    |||
    ||| As `"mid"` is not a column in the schema of `gradebook`,
    ||| Idris 2 proof search fails to find such a Field, so this
    ||| example fails type-checking, at compile-time.
    img : Image
    img = scatterPlot "mid" "final" gradebook

||| As both `"midterm"` and `"final"` *are* in the schema of
||| `gradebook`, and with the right types, this example type-checks
||| successfully.
img : Image
img = scatterPlot "midterm" "final" gradebook
