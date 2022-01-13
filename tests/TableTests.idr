module TableTests

import Test.Golden

main : IO ()
main = runner [
    MkTestPool "Table" [] Nothing [
        "Column", "Record", "Row", "Schema", "Table"
    ]
  ]
