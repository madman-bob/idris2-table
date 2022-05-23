module B2T2.Errors.UsingTables.BrownJellyBeans

import Data.Table

import B2T2.ExampleTables

failing "Can't find an implementation for Field schema \"color\" Bool."
    ||| Similarly to the midFinal example, the string literal
    ||| `"color"` fails to type-check, as Idris 2 proof search fails to
    ||| find a column of that name in the schema.
    |||
    ||| So this example fails at compile-time.
    countParticipants : Field schema color Bool
                     -> Table schema
                     -> Nat
    countParticipants color tbl = fst $ length $ filter (value "color") tbl

||| Referring instead to the `Field` variable, this example
||| type-checks successfully.
countParticipants : Field schema color Bool
                 -> Table schema
                 -> Nat
countParticipants color tbl = fst $ length $ filter (value color) tbl

result : Nat
result = countParticipants "brown" jellyAnon
