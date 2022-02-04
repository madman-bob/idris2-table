import Data.Table

0
EmployeeSchema : Schema
EmployeeSchema = [<"Last Name" :! String, "Department ID" :! Maybe Nat]

employees : Table EmployeeSchema
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

moreEmployees : Table EmployeeSchema
moreEmployees = [<robinson, smith, williams]

sameDepartment : Record EmployeeSchema -> Record EmployeeSchema -> Bool
sameDepartment [<_, x] [<_, y] = x == y

displayName : Record EmployeeSchema -> String
displayName [<lastName, Nothing] = lastName
displayName [<lastName, Just departmentID] = "\{lastName} (Dep. \{show departmentID})"

hasDepartment : Record EmployeeSchema -> Bool
hasDepartment [<lastName, Nothing] = False
hasDepartment [<lastName, Just departmentID] = True
