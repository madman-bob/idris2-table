module B2T2.ExamplePrograms.PHacking

import public Data.Table
import public B2T2.ExamplePrograms.PHacking.FisherTest

import B2T2.ExampleTables

%default total

public export
fisherTest : Field schema c1 Bool
          -> Field schema c2 Bool
          -> Table schema
          -> Double
fisherTest f1 f2 tbl = pValue $ contingencySquare f1 f2 tbl
  where
    contingencySquare : Field schema c1 Bool
                     -> Field schema c2 Bool
                     -> Table schema
                     -> ContingencySquare
    contingencySquare f1 f2 tbl = concat $ map (\rec => contingency (value f1 rec) (value f2 rec)) tbl

export
pHacking : {schema : Schema}
        -> AllColumns schema Bool
        => {baseCol : String}
        -> Field schema baseCol Bool
        -> Table schema
        -> IO ()
pHacking baseFld tbl = do
    for_ (allColumns schema) $ \(name ** fld) => if name == baseCol
        then pure ()
        else if fisherTest baseFld fld tbl < 0.05
            then putStrLn "We found a link between \{name} jelly beans and acne (p < 0.05)"
            else putStrLn "We found no link between \{name} jelly beans and acne (p > 0.05)"

export
pHackingHomogeneous : IO ()
pHackingHomogeneous = pHacking "get acne" jellyAnon

export
pHackingHeterogeneous : IO ()
pHackingHeterogeneous = pHacking "get acne" $ dropColumn "name" jellyNamed
