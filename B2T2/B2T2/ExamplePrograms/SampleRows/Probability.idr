module B2T2.ExamplePrograms.SampleRows.Probability

import System.Random

%default total

export
coin : HasIO io => {default 0.5 pHead : Double} -> io Bool
coin = map (< pHead) randomIO

-- True with probability k in n
export
in_ : HasIO io => Nat -> Nat -> io Bool
in_ k n = coin {pHead = cast k / cast n}
