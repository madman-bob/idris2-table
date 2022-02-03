import B2T2

export
main : IO ()
main = do
    for_ [1..300] $ \_ => do
        Element tbl hasRows <- sampleRows (frame students) 2
        printLn $ map (field "name") tbl
