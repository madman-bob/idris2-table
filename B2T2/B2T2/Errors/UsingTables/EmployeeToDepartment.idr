module B2T2.Errors.UsingTables.EmployeeToDepartment

import Data.Table

0
Department : Schema
Department = [<"Department ID" :! Nat, "Department Name" :! String]

0
Employee : Schema
Employee = [<"Last Name" :! String, "Department ID" :! Maybe Nat]

failing "Can't find an implementation for Field Department \"Last Name\" String."
    ||| To implement the type-signature of `lastNameToDeptId`, we need
    ||| to specify what sort of table we're using.
    |||
    ||| If we specify a `Department` table, then, similarly to the
    ||| midFinal example, the string literal `"Last Name"` fails to
    ||| type-check, as Idris 2 proof search fails to find a column of
    ||| that name in `Department`.
    |||
    ||| So this example fails at compile-time.
    |||
    ||| Misusing one sort of table as another is harder to hide when
    ||| you have to specify what sort of table you're using in the
    ||| type.
    lastNameToDeptId : Table Department
                    -> (name : String)
                    -> Maybe Nat
    lastNameToDeptId deptTab name = value "Department ID" <$> matchedRow
      where
        matchName : Record Department -> Bool
        matchName rec = value "Last Name" rec == name

        matchedTab : Table Department
        matchedTab = filter matchName deptTab

        matchedRow : Maybe (Record Department)
        matchedRow = case length matchedTab of
            (0 ** _) => Nothing
            (S _ ** _) => Just $ row matchedTab 0

failing "Mismatch between: Table (Employee :< (?name :! ?type)) and Maybe String."
    ||| Suppose we somehow have a working `lastNameToDeptId`.
    lastNameToDeptId : Table Department
                    -> (name : String)
                    -> Maybe Nat

    ||| Similarly to the previous example, we need to specify the
    ||| expected return type of `employeeToDepartment` to implement
    ||| its type-signature.
    |||
    ||| As the type returned by `buildColumn` does not match the
    ||| expected `Maybe String`, this example fails at compile-time.
    employeeToDepartment : (name : String)
                        -> (emplTab : Table Employee)
                        -> (deptTab : Table Department)
                        -> Maybe String
    employeeToDepartment name emplTab deptTab = buildColumn "Department Name" (\rec => lastNameToDeptId deptTab $ value "Last Name" rec) emplTab

failing "Mismatch between: Nat and String."
    ||| Suppose we somehow have a working `lastNameToDeptId`.
    lastNameToDeptId : Table Department
                    -> (name : String)
                    -> Maybe Nat

    ||| If we intended `employeeToDepartment` to return an `Employee`
    ||| table with an additional `Maybe String` column called
    ||| `"Department Name"`, we could indicate this by a return type of
    ||| `Table (Employee :< ("Department Name" :! Maybe String))`.
    |||
    ||| This example also fails at compile-time, due to the type
    ||| mismatch between the expected `Maybe String` required for the
    ||| `buildColumn`, and the `Maybe Nat` produced by
    ||| `lastNameToDeptId`.
    employeeToDepartment : (name : String)
                        -> (emplTab : Table Employee)
                        -> (deptTab : Table Department)
                        -> Table (Employee :< ("Department Name" :! Maybe String))
    employeeToDepartment name emplTab deptTab = buildColumn "Department Name" (\rec => lastNameToDeptId deptTab $ value "Last Name" rec) emplTab

||| As both `"Department Name"` and `"Department ID"` are in
||| `Department`, with the right types, this example type-checks
||| successfully.
deptIdToDeptName : (deptTab : Table Department)
                -> (deptId : Nat)
                -> Maybe String
deptIdToDeptName deptTab deptId = value "Department Name" <$> matchedRow
  where
    matchName : Record Department -> Bool
    matchName rec = value "Department ID" rec == deptId

    matchedTab : Table Department
    matchedTab = filter matchName deptTab

    matchedRow : Maybe (Record Department)
    matchedRow = case length matchedTab of
        (0 ** _) => Nothing
        (S _ ** _) => Just $ row matchedTab 0

||| As this example returns the right type, this example
||| type-checks successfully.
employeeToDepartment : (name : String)
                    -> (emplTab : Table Employee)
                    -> (deptTab : Table Department)
                    -> Maybe String
employeeToDepartment name emplTab deptTab = deptIdToDeptName deptTab !deptId
  where
    matchName : Record Employee -> Bool
    matchName rec = value "Last Name" rec == name

    matchedTab : Table Employee
    matchedTab = filter matchName emplTab

    matchedRow : Maybe (Record Employee)
    matchedRow = case length matchedTab of
        (0 ** _) => Nothing
        (S _ ** _) => Just $ row matchedTab 0

    deptId : Maybe Nat
    deptId = value "Department ID" !matchedRow
