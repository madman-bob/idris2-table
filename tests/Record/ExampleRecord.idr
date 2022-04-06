import Data.Table

StudentSchema : Schema
StudentSchema = [<"name" :! String, "age" :! Nat, "favorite color" :! String]

ResultsSchema : Schema
ResultsSchema = [<"quiz1" :! Nat, "quiz2" :! Nat]

exampleRecord : Record StudentSchema
exampleRecord = [<"Bob", 12, "blue"]

anotherRecord : Record StudentSchema
anotherRecord = [<"Alice", 17, "green"]

ambiguousRecord : Record [<"x" :! Nat, "x" :! String]
ambiguousRecord = [<0, "Hello, world"]
