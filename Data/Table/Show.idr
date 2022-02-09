module Data.Table.Show

import Data.Table.Schema
import public Data.Table.Schema.Quantifiers
import Data.Table.Record
import Data.Table.Data
import Data.Table.Row
import Data.SnocList

import Data.Vect
import Data.Nat
import Data.String

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

public export
data Alignment = L | R | C

align : Alignment -> (width : Nat) -> String -> String
align L width str = padRight width ' ' str
align R width str = padLeft  width ' ' str
align C width str = let delta = cast width - (cast $ length str) in
  if delta <= 0
  then str
  else let lft_delta = delta `div` 2
           rgt_delta = delta - lft_delta
       in (replicate (cast lft_delta) ' ') ++ str ++ (replicate (cast rgt_delta) ' ')

||| Print 1 row in the table,
printVect : (widths : Vect n Nat)
  -> (alignment : Vect n Alignment)
  -> Vect n String
  -> String
printVect widths alignment entries =
  pipeSeparate $ cast $
    zipWith3 (\algn,n,str => align algn n str) alignment widths entries

export
showTable : {schema : Schema} ->
  ShowSchema schema =>
  (alignment : Vect (length schema) Alignment)
  -> Table schema -> String
showTable alignment table =
  let header = nameVect schema
      rows   = map showRecord table
      maxWidths = foldr (\xs,acc => zipWith max (map length xs) acc)
                    (map length header) rows
  in unlines $ "" -- Empty first line makes printing alignment a little nicer
            :: (printVect maxWidths alignment header)
            :: (ruler $ cast maxWidths)
            :: ((the _ $ map (printVect maxWidths alignment) rows) <>> [])

export
{schema : Schema} -> ShowSchema schema => Show (Table schema) where
  show = showTable (replicate (length schema) L)

students : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
students = [<
    [<"Bob",    8, "blue" ],
    [<"Alice", 17, "green"],
    [<"Eve",   13, "red"  ]
  ]
