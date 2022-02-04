module B2T2.ExamplePrograms.PHacking

import public Data.Table
import public B2T2.ExamplePrograms.PHacking.FisherTest

import B2T2.ExampleTables

%default total

public export
fisherTest : (0 c1 : String)
          -> HasField schema c1 Bool
          => (0 c2 : String)
          -> HasField schema c2 Bool
          => Table schema
          -> Double
fisherTest c1 c2 tbl = pValue $ contingencySquare c1 c2 tbl
  where
    contingencySquare : (0 c1 : String)
                     -> HasField schema c1 Bool
                     => (0 c2 : String)
                     -> HasField schema c2 Bool
                     => Table schema
                     -> ContingencySquare
    contingencySquare c1 c2 tbl = concat $ map (\rec => contingency (field c1 rec) (field c2 rec)) tbl

export
pHacking : {schema : Schema}
        -> AllColumns schema Bool
        => (baseCol : String)
        -> HasField schema baseCol Bool
        => Table schema
        -> IO ()
pHacking baseCol tbl = do
    for_ (allColumns schema) $ \(name ** _) => if name == baseCol
        then pure ()
        else if fisherTest baseCol name tbl < 0.05
            then putStrLn "We found a link between \{name} jelly beans and acne (p < 0.05)"
            else putStrLn "We found no link between \{name} jelly beans and acne (p > 0.05)"

export
pHackingHomogeneous : IO ()
pHackingHomogeneous = pHacking "get acne" jellyAnon

export
pHackingHeterogeneous : IO ()
pHackingHeterogeneous = pHacking "get acne" $ dropColumn "name" jellyNamed
