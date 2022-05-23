module B2T2.Errors.UsingTables.FavoriteColor

import Data.Table

failing "Mismatch between: String and Bool."
    ||| The table `filter` function expects its inner function to
    ||| return a Bool, but the `"favorite color"` field is a String.
    |||
    ||| So this example fails to type-check at compile-time.
    |||
    ||| Idris 2 then attempts to try all other `filter` functions in
    ||| scope, resulting in an elaboration error, as none of them work.
    participantsLikeGreen : Field schema "favorite color" String
                         => Table schema
                         -> Table schema
    participantsLikeGreen = filter $ \rec => value "favorite color" rec

||| When the inner function instead returns a Bool, this example
||| type-checks successfully.
participantsLikeGreen : Field schema "favorite color" String
                     => Table schema
                     -> Table schema
participantsLikeGreen = filter $ \rec => value "favorite color" rec == "green"
