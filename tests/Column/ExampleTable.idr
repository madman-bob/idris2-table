import Data.Table

students : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
students = [<
    [<"Bob",   12, "blue" ],
    [<"Alice", 17, "green"],
    [<"Eve",   13, "red"  ]
  ]

grade : Nat -> String
grade n = case n `div` 10 of
    10 => "A+"
    9 => "A+"
    8 => "A"
    7 => "B"
    6 => "C"
    5 => "D"
    _ => "F"
