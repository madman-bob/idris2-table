import Data.Table

0
EmployeeSchema : Schema
EmployeeSchema = [<"Last Name" :! String, "Department ID" :! Maybe Nat]

0
DepartmentSchema : Schema
DepartmentSchema = [<"Department ID" :! Nat, "Department Name" :! String, "Manager" :! String]

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

sales : Record DepartmentSchema
sales = [<31, "Sales", "Harriet"]

finance : Record DepartmentSchema
finance = [<32, "Finance", "George"]

production : Record DepartmentSchema
production = [<33, "Production", "Charles"]

rowFromEnd : Frame schema n -> Fin n -> Record schema
rowFromEnd frm k = rowFromEnd (table frm) k
