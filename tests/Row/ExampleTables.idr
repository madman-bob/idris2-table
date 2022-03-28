import Data.Table

0
EmployeeSchema : Schema
EmployeeSchema = [<"Last Name" :! String, "Department ID" :! Maybe Nat]

0
DepartmentSchema : Schema
DepartmentSchema = [<"Department ID" :! Nat, "Department Name" :! String, "Manager" :! String]

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

sales : Record DepartmentSchema
sales = [<31, "Sales", "Harriet"]

finance : Record DepartmentSchema
finance = [<32, "Finance", "George"]

production : Record DepartmentSchema
production = [<33, "Production", "Charles"]

sameDepartment : Record EmployeeSchema -> Record EmployeeSchema -> Bool
sameDepartment [<_, x] [<_, y] = x == y

displayName : Record EmployeeSchema -> String
displayName [<lastName, Nothing] = lastName
displayName [<lastName, Just departmentID] = "\{lastName} (Dep. \{show departmentID})"

hasDepartment : Record EmployeeSchema -> Bool
hasDepartment [<lastName, Nothing] = False
hasDepartment [<lastName, Just departmentID] = True

colorWarmth : String -> String
colorWarmth color = ifThenElse (color == "red") "warm" "cool"

average : List Nat -> Double
average xs = (cast $ sum xs) / (cast $ length xs)

mFloor : Nat -> Nat -> Nat
mFloor n k = minus k $ mod k n

Cast Bool Nat where
    cast False = 0
    cast True = 1
