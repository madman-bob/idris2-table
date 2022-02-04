import Data.Table

StudentSchema : Schema
StudentSchema = [<"name" :! String, "age" :! Nat, "favorite color" :! String]

students : Table StudentSchema
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
