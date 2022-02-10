import Data.Table

EmployeeSchema : Schema
EmployeeSchema = [<"Last Name" :! String, "Department ID" :! Maybe Nat]

employees : Frame EmployeeSchema 3
employees = [<
    [<"Rafferty",   Just 31],
    [<"Jones",      Just 32],
    [<"Heisenberg", Just 33]
  ]

robinson : Record EmployeeSchema
robinson = [<"Robinson", Just 34]

smith : Record EmployeeSchema
smith = [<"Smith", Just 34]

williams : Record EmployeeSchema
williams = [<"Williams", Nothing]

moreEmployees : Frame EmployeeSchema 3
moreEmployees = [<robinson, smith, williams]

rowFromEnd : Frame schema n -> Fin n -> Record schema
rowFromEnd frm k = rowFromEnd (table frm) k
