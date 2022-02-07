module B2T2.ExamplePrograms.GroupBy

import public Data.Table
import Data.SortedMap

import B2T2.ExampleTables

%default total

export
groupByGeneral : Field schema keyCol a
              -> Ord a
              => (Record schema -> Record groupSchema)
              -> Table schema
              -> Table [<"key" :! a, "groups" :! Table groupSchema]
groupByGeneral keyFld f tbl = mapToTable $ foldr addRow empty tbl
  where
    addVal : k -> v -> SortedMap k (List v) -> SortedMap k (List v)
    addVal key val map = insert key (val :: maybe [] id (lookup key map)) map

    addRow : Record schema -> SortedMap a (List $ Record groupSchema) -> SortedMap a (List $ Record groupSchema)
    addRow rec = addVal (value keyFld rec) (f rec)

    mapToTable : SortedMap a (List $ Record groupSchema) -> Table [<"key" :! a, "groups" :! Table groupSchema]
    mapToTable map = mkTable $ Prelude.map (\(key, recs) => [<key, mkTable recs]) $ SortedMap.toList map

export
groupByRetentive : Ord a
                => Field schema keyCol a
                -> Table schema
                -> Table [<"key" :! a, "groups" :! Table schema]
groupByRetentive keyFld = groupByGeneral keyFld id

export
groupedEmployeesRetentive : Table [<"key" :! Maybe Nat, "groups" :! Table [<"Last Name" :! String, "Department ID" :! Maybe Nat]]
groupedEmployeesRetentive = groupByRetentive "Department ID" employees

export
groupBySubtractive : Ord a
                  => (keyFld : Field schema keyCol a)
                  -> Table schema
                  -> Table [<"key" :! a, "groups" :! Table (drop schema keyFld)]
groupBySubtractive keyFld = groupByGeneral keyFld (dropField keyFld)

export
groupedEmployeesSubtractive : Table [<"key" :! Maybe Nat, "groups" :! Table [<"Last Name" :! String]]
groupedEmployeesSubtractive = groupBySubtractive "Department ID" employees
