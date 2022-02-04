module B2T2.ExamplePrograms.PHacking.FisherTest

%default total

||| A 2x2 contingency table
public export
record ContingencySquare where
    constructor MkContingencySquare
    a : Nat
    b : Nat
    c : Nat
    d : Nat

%name ContingencySquare sqr

public export
contingency : Bool -> Bool -> ContingencySquare
contingency False False = MkContingencySquare 1 0 0 0
contingency False True = MkContingencySquare 0 1 0 0
contingency True False = MkContingencySquare 0 0 1 0
contingency True True = MkContingencySquare 0 0 0 1

public export
Semigroup ContingencySquare where
    x <+> y = MkContingencySquare (x.a + y.a) (x.b + y.b) (x.c + y.c) (x.d + y.d)

public export
Monoid ContingencySquare where
    neutral = MkContingencySquare 0 0 0 0

public export
pValue : ContingencySquare -> Double
pValue (MkContingencySquare a b c d) = go a b c d
  where
    go : Nat -> Nat -> Nat -> Nat -> Double
    go 0 0 c d = 1
    go 0 (S b) c d = (cast $ S b + d) / (cast $ S b + c + d) * go 0 b c d
    go (S a) b c d = (cast $ S a + b) / (cast $ S a) * (cast $ S a + c) / (cast $ S a + b + c + d) * go a b c d
