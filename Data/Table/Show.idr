module Data.Table.Show

import Data.Table.Schema
import public Data.Table.Schema.Quantifiers
import Data.Table.Record
import Data.Table.Data
import Data.Table.Row
import Data.SnocList
import Data.Table.Row.Frame

import Data.Vect
import Data.Nat
import Data.String

import Syntax.PreorderReasoning

||| A schema whose rows are all instances of Show
public export
ShowSchema : Schema -> Type
ShowSchema schema = All (\col => Show (snd col)) schema

-- Would be natural to use a SnocVect, but stdlib doesn't have it yet
showRecordAux : (acc : Vect k String) ->
  ShowSchema schema => (Record schema) -> Vect (length schema + k) String
showRecordAux acc [<] = acc
showRecordAux acc @{all :< showCurrent} (rec :< fld) =
  replace {p = \n => Vect n String} (sym $ plusSuccRightSucc _ _)
  $ showRecordAux (show fld :: acc) rec

showRecord : ShowSchema schema => (Record schema) -> Vect (length schema) String
showRecord = rewrite sym $ plusZeroRightNeutral (length schema) in
  showRecordAux []

nameVectAux : (acc : Vect k String) -> (schema : Schema) -> Vect (length schema + k) String
nameVectAux acc [<] = acc
nameVectAux acc (schema :< x) =
  replace {p = \n => Vect n String} (sym $ plusSuccRightSucc _ _)
  $ nameVectAux (fst x :: acc) schema

nameVect : (schema : Schema) -> Vect (length schema) String
nameVect schema = rewrite sym $ plusZeroRightNeutral (length schema) in
  (nameVectAux [] schema)

Cast (Vect n a) (List a) where
  cast [] = []
  cast (x :: xs) = x :: cast xs

||| Pipe separated string
pipeSeparate : List String -> String
pipeSeparate strs = "| \{concat $ intersperse " | " $ strs} |"

||| Pipe separated ruler
ruler : List Nat -> String
ruler = pipeSeparate . (map $ flip replicate '-')

namespace Horizontal
  public export
  data Alignment = L | R | C

namespace Vertical
  public export
  data Alignment = T | B | C


halign : Horizontal.Alignment -> (width : Nat) -> String -> String
halign L width str = padRight width ' ' str
halign R width str = padLeft  width ' ' str
halign C width str = let delta = cast width - (cast $ length str) in
  if delta <= 0
  then str
  else let lft_delta = delta `div` 2
           rgt_delta = delta - lft_delta
       in (replicate (cast lft_delta) ' ') ++ str ++ (replicate (cast rgt_delta) ' ')

take : (len : Nat) -> List a -> (n : Nat ** m : Nat ** prf : m + n = len ** Vect n a)
take 0 xs = (0 ** 0 ** Refl ** [])
take len@(S _) [] = (0 ** len ** plusZeroRightNeutral _ ** [])
take (S len) (x :: xs) =
  let (n ** m ** prf ** ys) = Show.take len xs in
  (S n ** m ** Calc $
    |~ m + (1 + n)
    ~~ 1 + (m + n) ...(sym $ plusSuccRightSucc _ _)
    ~~ 1 +  len    ...(cong (1+) prf)
  ** x :: ys)

halve : (n : Nat) -> (big : Nat ** small : Nat ** big + small = n)
halve 0 = (0 ** 0 ** Refl)
halve 1 = (1 ** 0 ** Refl)
halve (S $ S n) =
  let (big ** small ** prf) = halve n in
  (S big ** S small ** Calc $
    |~ 1 + (big + (1 + small))
    ~~ 2 + (big + small) ...(cong (1+) $ sym $ plusSuccRightSucc _ _)
    ~~ 2 + n ...(cong (2+) prf))

valign : Vertical.Alignment -> (height : Nat) -> List String -> Vect height String
valign algn height xs =
  let (m ** n ** prf ** ys) = Show.take height xs
      (big ** small ** prf') : (big : Nat ** small : Nat ** big + small = n) = case algn of
        T => (0 ** n ** Refl)
        B => (n ** 0 ** plusZeroRightNeutral _)
        C => halve n
      result = (replicate big "") ++ ys ++ (replicate small "")
      correct = Calc $
        |~ big + (m + small)
        ~~ big + (small + m) ...(cong (big +) $ plusCommutative _ _)
        ~~(big + small) + m  ...(plusAssociative _ _ _)
        ~~ n + m             ...(cong (+m) prf')
        ~~ height            ...(prf)
  in replace {p = \k => Vect k String} correct
     result
||| Print 1 row in the table,
printVect : (widths : Vect n Nat)
  -> (halignment : Vect n Horizontal.Alignment)
  -> (valignment : Vect n   Vertical.Alignment)
  -> Vect n String
  -> List String
printVect widths halignment valignment entries =
  let u = map lines entries
      w = map List.length u
      m = foldr max 1 w
      k = cast {to = List _} $ transpose $ zipWith (\v => valign v m) valignment u
  in map (\entries => pipeSeparate $ cast $
    zipWith3 (\algn,n,str => halign algn n str) halignment widths entries) k

export
showTable : {schema : Schema} ->
  ShowSchema schema
  => {default (replicate (length schema) L) halignment : Vect (length schema) Horizontal.Alignment}
  -> {default (replicate (length schema) T) valignment : Vect (length schema) Vertical.Alignment}
  -> Table schema -> String
showTable {halignment,valignment} table =
  let header = nameVect schema
      rows   = map showRecord table
      maxWidths = foldr (\xs,acc => zipWith max (map length xs) acc)
                    (map length header) rows
  in unlines $ "" -- Empty first line makes printing alignment a little nicer
            :: (printVect maxWidths halignment valignment header)
            ++ (ruler $ cast maxWidths)
            :: foldMap (printVect maxWidths halignment valignment) rows

{-
||| If we don't have access to the schema, we can still show the body
||| of the table.
export
showTableBody :
  (allShow : ShowSchema schema) =>
  {default (replicate (length allShow) L) alignment : Vect (length allShow) Horizontal.Alignment}
  -> Table schema -> String
-- Reconstruct the number of columns from the show instance :D
showTableBody {alignment} table =
  let rows   = replace {p = \n => SnocList (Vect n String)}
                       (sym $ lengthAllLengthSchema allShow)
                       (map showRecord table)
      maxWidths = foldr (\xs,acc => zipWith max (map String.length xs) acc)
                    (replicate _ 1) rows
  in unlines $ "" -- Empty first line makes printing alignment a little nicer
            :: (ruler $ cast maxWidths)
            :: ((the _ $ map (printVect maxWidths alignment) rows) <>> [])
-}
export
{schema : Schema} -> ShowSchema schema => Show (Table schema) where
  show = showTable

students : Table [<"name" :! String, "age" :! Nat, "favorite\ncolor" :! String]
students = [<
    [<"Bob",    8, "blue" ],
    [<"Alice", 17, "green"],
    [<"Eve",   13, "red"  ]
  ]
{-
export
showFrame : {schema : Schema} ->
  ShowSchema schema =>
  {default (replicate (length schema) L) alignment : Vect (length schema) Horizontal.Alignment}
  -> Frame schema n -> String
showFrame {alignment} frame = showTable {alignment} frame.fst

||| If we don't have access to the schema, we can still show the body
||| of the table.
export
showFrameBody :
  (allShow : ShowSchema schema) =>
  {default (replicate (length allShow) L) alignment : Vect (length allShow) Horizontal.Alignment}
  -> Frame schema n -> String
showFrameBody {alignment} frame = showTableBody {alignment} frame.fst
-}

gradebookTable : Table [<
    "name" :! String,
    "age" :! Nat,
    "quizzes" :! Table [<"quiz#" :! Nat, "grade" :! Nat],
    "midterm" :! Nat,
    "final" :! Nat
  ]
gradebookTable = [<
    [<"Bob",   12, [<[<1, 8],
                     [<2, 9],
                     [<3, 7],
                     [<4, 9]], 77, 87],

    [<"Alice", 17, [<[<1, 6],
                     [<2, 8],
                     [<3, 8],
                     [<4, 7]], 88, 85],

    [<"Eve",   13, [<[<1, 7],
                     [<2, 9],
                     [<3, 8],
                     [<4, 8]], 84, 77]
  ]
