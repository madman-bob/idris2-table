module B2T2.ExamplePrograms.QuizScoreFilter

import public Data.String
import public Data.Table

import B2T2.ExampleTables

%default total

public export
data GradebookColumn : String -> Type -> Type -> Type where
    QuizCol : So (isPrefixOf "quiz" name) -> GradebookColumn name a a
    NoQuizCol : So (not $ isPrefixOf "quiz" name) -> GradebookColumn name type a

public export
data GradebookSchema : (schema : Schema) -> (a : Type) -> Type where [search schema]
    Lin : GradebookSchema [<] a
    (:<) : GradebookSchema schema a -> GradebookColumn name type a -> GradebookSchema (schema :< (name :! type)) a

public export
quizCount : (0 schema : Schema)
         -> GradebookSchema schema a
         => Nat
quizCount [<] @{[<]} = 0
quizCount (schema :< _) @{_ :< QuizCol _} = S $ quizCount schema
quizCount (schema :< _) @{_ :< NoQuizCol _} = quizCount schema

public export
quizTotal : GradebookSchema schema a
         => Num a
         => Record schema
         -> a
quizTotal @{[<]} [<] = 0
quizTotal @{_ :< QuizCol _} (rec :< quizScore) = quizTotal rec + quizScore
quizTotal @{_ :< NoQuizCol _} (rec :< _) = quizTotal rec

public export
quizAverage : GradebookSchema schema Nat
           => Record schema
           -> Double
quizAverage rec = (cast $ quizTotal rec) / (cast $ quizCount schema)

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
gradebookWithAverage = buildColumn "average-quiz" quizAverage gradebook
