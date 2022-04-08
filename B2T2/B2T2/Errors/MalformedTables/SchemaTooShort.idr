module B2T2.Errors.MalformedTables.SchemaTooShort

import Data.Table

failing "While processing right hand side of students. Sorry, I can't find any elaboration which works. All errors:"
    ||| Similarly to the missingRow and missingCell examples, a row
    ||| with three elements does not type-check against a schema with
    ||| two entries. So Idris 2 tries all other uses of SnocList
    ||| notation in scope, in case one of them works.
    |||
    ||| As none of them do, this fails at compile-time, with the above
    ||| error message.
    students : Table [<"name" :! String, "age" :! Nat]
    students = [<
        [<"Bob",   12, "blue" ],
        [<"Alice", 17, "green"],
        [<"Eve",   13, "red"  ]
      ]
