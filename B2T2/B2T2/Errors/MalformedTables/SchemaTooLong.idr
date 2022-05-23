module B2T2.Errors.MalformedTables.SchemaTooLong

import Data.Table

failing "While processing right hand side of students. Sorry, I can't find any elaboration which works. All errors:"
    ||| Similarly to the missingRow, missingCell, and schemaTooShort
    ||| examples, a row with three elements does not type-check against
    ||| a schema with four entries. So Idris 2 tries all other uses of
    ||| SnocList notation in scope, in case one of them works.
    |||
    ||| As none of them do, this fails at compile-time, with the above
    ||| error message.
    students : Table [<"name" :! String, "age" :! Nat, "favorite number" :! Nat, "favorite color" :! String]
    students = [<
        [<"Bob",   12, "blue" ],
        [<"Alice", 17, "green"],
        [<"Eve",   13, "red"  ]
      ]
