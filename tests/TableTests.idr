module TableTests

import Test.Golden

main : IO ()
main = runner [
    !(testsInDir "B2T2" (const True) "B2T2 Tests" [] Nothing),
    !(testsInDir "." (const True) "Table" [] Nothing)
  ]
