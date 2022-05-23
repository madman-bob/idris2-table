module B2T2.Errors.UsingTables.BlackAndWhite

import Data.Table

import B2T2.ExampleTables

failing "Can't find an implementation for Field"
    ||| Similarly to the midFinal example, the string literal
    ||| `"black and white"` fails to type-check, as Idris 2 proof
    ||| search fails to find a column of that name in the schema of
    ||| `jellyAnon`.
    |||
    ||| So this example fails at compile-time.
    jellyBW : Table [<
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
        "eat black and white" :! Bool
      ]
    jellyBW = buildColumn "eat black and white" (\rec => value "black and white" rec == True) jellyAnon

||| As both `"black"` and `"white"` *are* in the schema of
||| `jellyAnon`, and with the right types, this example type-checks
||| successfully.
jellyBW : Table [<
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
    "eat black and white" :! Bool
  ]
jellyBW = buildColumn "eat black and white" (\rec => value "black" rec && value "white" rec) jellyAnon
