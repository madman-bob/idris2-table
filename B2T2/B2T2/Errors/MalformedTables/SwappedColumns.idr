module B2T2.Errors.MalformedTables.SwappedColumns

import Data.Table

failing "While processing right hand side of students. Can't find an implementation for FromString Nat."
    ||| Idris 2 attempts to check the types of the cells against the
    ||| schema, starting at the lower-right.
    |||
    ||| The cell `"red"` type-checks ok, but it then tries to check
    ||| that `"Eve"` is a Nat, as required by the schema.
    |||
    ||| As Idris 2 allows overloading of String literals, it attempts
    ||| to find an overload of String literals that can produce a Nat.
    |||
    ||| As no such overload exists, this fails at compile-time, with
    ||| the above error message.
    students : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
    students = [<
        [<12, "Bob",   "blue" ],
        [<17, "Alice", "green"],
        [<13, "Eve",   "red"  ]
      ]
