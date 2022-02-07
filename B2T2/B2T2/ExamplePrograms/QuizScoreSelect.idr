module B2T2.ExamplePrograms.QuizScoreSelect

import public Data.Table

import B2T2.ExampleTables

%default total

public export
data HasQuizzes : (schema : Schema) -> (n : Nat) -> (a : Type) -> Type where [search schema n]
    Lin : HasQuizzes schema 0 a
    (:<) : HasQuizzes schema n a -> Field schema ("quiz" ++ cast (S n)) a -> HasQuizzes schema (S n) a

public export
quizTotal : (0 n : Nat)
         -> HasQuizzes schema n a
         => Num a
         => Record schema
         -> a
quizTotal 0 @{[<]} rec = 0
quizTotal (S n) @{_ :< fld} rec = quizTotal n rec + value fld rec

public export
quizAverage : (n : Nat)
           -> HasQuizzes schema n Nat
           => Record schema
           -> Double
quizAverage n rec = (cast $ quizTotal n rec) / cast n

export
gradebookWithAverage : Table [<
    "name" :! String,
    "age" :! Nat,
    "quiz1" :! Nat,
    "quiz2" :! Nat,
    "midterm" :! Nat,
    "quiz3" :! Nat,
    "quiz4" :! Nat,
    "final" :! Nat,
    "average-quiz" :! Double
  ]
gradebookWithAverage = buildColumn "average-quiz" (quizAverage 4) gradebook
