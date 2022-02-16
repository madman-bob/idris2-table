module B2T2.ExampleAPI

import Data.Table
import B2T2.TableAPI
import B2T2.ExampleTables

%default total

s1 : ?t1
s1 = addRows students [ [<"Colton", 19, "blue"] ]

s2 : ?t2
s2 = addRows gradebook []

s3 : ?t3
s3 = addColumn students "hair-color" [<"brown", "red", "blonde"]

s4 : ?t4
s4 = addColumn gradebook "presentation" [<9, 9, 6]

-- s5 : ?t5
-- s5 = buildColumn students "is-teenager" (\r => r)

