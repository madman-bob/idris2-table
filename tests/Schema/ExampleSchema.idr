import Data.Table

exampleSchema : Schema
exampleSchema = [<"name" :! String, "age" :! Nat, "favorite color" :! String]

additionalColumns : Schema
additionalColumns = [<"quiz1" :! Nat, "quiz2" :! Nat]
