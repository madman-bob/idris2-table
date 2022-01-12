module TableTests

import Test.Golden

main : IO ()
main = runner [
    MkTestPool "Table" [] Nothing [
        "Record", "Row", "Schema", "Table"
    ]
  ]
