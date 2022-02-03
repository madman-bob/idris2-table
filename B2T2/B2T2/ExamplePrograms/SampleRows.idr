module B2T2.ExamplePrograms.SampleRows

import Data.Fin.Extra

import public B2T2.ExamplePrograms.SampleRows.Probability
import B2T2.ExampleTables

%default total

export
sampleRows : HasIO io
          => {n : Nat}
          -> (frm : Frame schema n)
          -> (k : Fin (S n))
          -> io (Frame schema (cast k))
sampleRows frm FZ = pure [<]
sampleRows {n = n@(S _)} frm k@(FS j) = case strengthen' j of
    Left Refl => pure $
        replace {p = Frame _} (cong S $ sym finToNatLastIsBound)
        frm
    Right (j' ** prf) => case !(cast k `in_` n) of
        False =>
            replace {p = io . Frame _} (cong S $ sym prf) $
            sampleRows (init frm) (FS j')
        True =>
            [| sampleRows (init frm) j :< (pure $ last frm) |]
