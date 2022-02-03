module TableTests

import Test.Golden

main : IO ()
main = runner [
    MkTestPool "Table" [] Nothing [
        "Column", "Frame", "Record", "Row", "Schema", "Table"
    ]
  ]
