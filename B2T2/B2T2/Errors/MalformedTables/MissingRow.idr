module B2T2.Errors.MalformedTables.MissingRow

import Data.Table

failing "While processing right hand side of students. Sorry, I can't find any elaboration which works. All errors:"
    ||| The empty row is represented as `[<]`, using the Idris 2
    ||| SnocList notation.
    |||
    ||| As the empty row does not type-check in a Table with a
    ||| non-empty schema, Idris 2 tries all the other uses of SnocList
    ||| notation in scope as well, in case one of them works.
    |||
    ||| As none of them do, this fails at compile-time, with the above
    ||| error message.
    students : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
    students = [<
        [<"Bob",   12, "blue" ],
        [<"Alice", 17, "green"],
        [<]
      ]
