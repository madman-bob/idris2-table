module B2T2.Errors.MalformedTables.MissingCell

import Data.Table

failing "While processing right hand side of students. Sorry, I can't find any elaboration which works. All errors:"
    ||| Similarly to the missingRow example, as a row with two Strings
    ||| does not type-check against the given schema, Idris 2 tries all
    ||| the other uses of SnocList notation in scope, in case one of
    ||| them works.
    |||
    ||| As none of them do, this fails at compile-time, with the above
    ||| error message.
    students : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
    students = [<
        [<"Bob",   "blue"         ],
        [<"Alice", 17,     "green"],
        [<"Eve",   13,     "red"  ]
      ]
