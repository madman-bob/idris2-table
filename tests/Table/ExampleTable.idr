import Data.Table

students : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
students = [<
    [<"Bob",   12, "blue" ],
    [<"Alice", 17, "green"],
    [<"Eve",   13, "red"  ]
  ]
