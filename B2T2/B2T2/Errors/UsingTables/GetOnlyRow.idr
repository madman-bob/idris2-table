module B2T2.Errors.UsingTables.GetOnlyRow

import Data.Table

import B2T2.ExampleTables

failing "Can't find an implementation for So (with block in integerLessThanNat 1 False 1)."
    ||| The `row` function requires a proof that the given index is in
    ||| range for that table.
    |||
    ||| As the table `students` is known at compile-time, Idris 2 is
    ||| able to work out that the result of the filter has one row.
    |||
    ||| To try and generate the proof that the index `1` is in range,
    ||| Idris 2 needs a proof that `index < rowCount`. Which in this
    ||| case, is a proof that `1 < 1`.
    |||
    ||| As Idris 2 cannot find such a proof, this example fails at
    ||| compile-time.
    aliceFavoriteColor : String
    aliceFavoriteColor = value "favorite color" $ row (filter (\student => value "name" student == "Alice") students) 1

||| In this example, Idris 2 instead needs a proof that `0 < 1`,
||| which it is able to generate automatically.
|||
||| So this example type-checks successfully.
aliceFavoriteColor : String
aliceFavoriteColor = value "favorite color" $ row (filter (\student => value "name" student == "Alice") students) 0
