module B2T2.Errors.UsingTables.BrownGetAcne

import Data.Table

import B2T2.ExampleTables

count : Ord a
     => Field schema name a
     -> Table schema
     -> Table [<"value" :! a, "count" :! Nat]

failing "Can't find an implementation for Field"
    brownAndGetAcneTable : Table [<
        "name" :! String,
        "get acne" :! Bool,
        "red" :! Bool,
        "black" :! Bool,
        "white" :! Bool,
        "green" :! Bool,
        "yellow" :! Bool,
        "brown" :! Bool,
        "orange" :! Bool,
        "pink" :! Bool,
        "purple" :! Bool,
        "part2" :! Bool
      ]
    brownAndGetAcneTable = buildColumn "part2" (\rec => value "brown" rec && value "get acne" rec) jellyNamed

    ||| Similarly to the midFinal example, the string literal
    ||| `"brown and get acne"` fails to type-check, as Idris 2 proof
    ||| search fails to find a column of that name in the schema of
    ||| brownAndGetAcneTable. So this example fails at compile-time.
    result : Table [<"value" :! Bool, "count" :! Nat]
    result = count "brown and get acne" brownAndGetAcneTable

brownAndGetAcneTable : Table [<
    "name" :! String,
    "get acne" :! Bool,
    "red" :! Bool,
    "black" :! Bool,
    "white" :! Bool,
    "green" :! Bool,
    "yellow" :! Bool,
    "brown" :! Bool,
    "orange" :! Bool,
    "pink" :! Bool,
    "purple" :! Bool,
    "brown and get acne" :! Bool
  ]
brownAndGetAcneTable = buildColumn "brown and get acne" (\rec => value "brown" rec && value "get acne" rec) jellyNamed

||| Once the name of the new column in brownAndGetAcneTable is
||| corrected, this example type-checks successfully.
result : Table [<"value" :! Bool, "count" :! Nat]
result = count "brown and get acne" brownAndGetAcneTable
