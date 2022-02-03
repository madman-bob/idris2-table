module TableTests

import Test.Golden

main : IO ()
main = runner [
    !(testsInDir "B2T2" (const True) "B2T2 Tests" [] Nothing),
    MkTestPool "Table" [] Nothing [
        "Column", "Frame", "Record", "Row", "Schema", "Table"
    ]
  ]
