module B2T2.Errors.MalformedTables.MissingSchema

import Data.Table

failing "Can't find an implementation for Show (Table [<(?name :! String), (?name :! Integer), (?name :! String)])."
    ||| While we cannot express a Table without a schema, we can
    ||| express a Table without an *explicit* schema.
    |||
    ||| In the following example, we use the function call
    ||| `the (Table _)`to tell Idris 2 that the following expression is
    ||| a Table, without telling it the schema.
    |||
    ||| We then call `show` on this Table, which requires a `Show`
    ||| interface for it.
    |||
    ||| But the default `Show` interface for a Table requires its
    ||| schema. So this fails at compile-time, with the above error
    ||| message.
    |||
    ||| Note that Idris 2 can infer much of the schema, with the
    ||| column names (the `?name` holes) being the only thing it cannot
    ||| infer.
    main : IO ()
    main = putStrLn $ show $ the (Table _) [<
        [<"Bob",   12, "blue" ],
        [<"Alice", 17, "green"],
        [<"Eve",   13, "red"  ]
      ]
