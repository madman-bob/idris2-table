import Data.Table

StudentSchema : Schema
StudentSchema = [<"name" :! String, "age" :! Nat, "favorite color" :! String]

exampleRecord : Record StudentSchema
exampleRecord = [<"Bob", 12, "blue"]

anotherRecord : Record StudentSchema
anotherRecord = [<"Alice", 17, "green"]
