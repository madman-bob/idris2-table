module Data.Table.Show

import Data.String
import public Data.Vect

import Syntax.PreorderReasoning

import public Data.Table.Schema.Quantifiers
import public Data.Table.Data
import Data.Table.Row

public export
ShowField : FieldSchema -> Type
ShowField (_ :! type) = Show type

||| A schema whose columns are all instances of Show
public export
ShowSchema : Schema -> Type
ShowSchema schema = All ShowField schema

-- Would be natural to use a SnocVect, but stdlib doesn't have it yet
showRecordAux : (acc : Vect k String)
             -> ShowSchema schema
             => Record schema
             -> Vect (length schema + k) String
showRecordAux acc [<] = acc
showRecordAux acc @{_ :< _} (rec :< fld) =
    replace {p = \n => Vect n String} (sym $ plusSuccRightSucc _ _) $
    showRecordAux (show fld :: acc) rec

showRecord : ShowSchema schema
          => Record schema
          -> Vect (length schema) String
showRecord rec =
    replace {p = \n => Vect n String} (plusZeroRightNeutral _) $
    showRecordAux [] rec

nameVectAux : (acc : Vect k String)
           -> (schema : Schema)
           -> Vect (length schema + k) String
nameVectAux acc [<] = acc
nameVectAux acc (schema :< (name :! _)) =
    replace {p = \n => Vect n String} (sym $ plusSuccRightSucc _ _) $
    nameVectAux (name :: acc) schema

nameVect : (schema : Schema)
        -> Vect (length schema) String
nameVect schema =
    replace {p = \n => Vect n String} (plusZeroRightNeutral _) $
    nameVectAux [] schema

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

||| Take first `len` elements of the list, but return how many you
||| took, and how many are left
take : (len : Nat) -> List a -> (n : Nat ** m : Nat ** prf : m + n = len ** Vect n a)
take 0 xs = (0 ** 0 ** Refl ** [])
take len@(S _) [] = (0 ** len ** plusZeroRightNeutral _ ** [])
take (S len) (x :: xs) =
    let (n ** m ** prf ** ys) = Show.take len xs in
    (S n ** m ** Calc $
        |~ m + (1 + n)
        ~~ 1 + (m + n) ...(sym $ plusSuccRightSucc _ _)
        ~~ 1 +  len    ...(cong (1 +) prf)
    ** x :: ys)

halve : (n : Nat) -> (small : Nat ** big : Nat ** small + big = n)
halve 0 = (0 ** 0 ** Refl)
halve 1 = (0 ** 1 ** Refl)
halve (S $ S n) =
    let (small ** big ** prf) = halve n in
    (S small ** S big ** Calc $
        |~ 1 + (small + (1 + big))
        ~~ 2 + (small + big) ...(cong (1 +) $ sym $ plusSuccRightSucc _ _)
        ~~ 2 + n ...(cong (2 +) prf))

valign : Vertical.Alignment -> (height : Nat) -> List String -> Vect height String
valign algn height xs =
    let (m ** n ** prf ** ys) = Show.take height xs
        (small ** big ** prf') : (small : Nat ** big : Nat ** small + big = n) = case algn of
          T => (0 ** n ** Refl)
          B => (n ** 0 ** plusZeroRightNeutral _)
          C => halve n
        result = (replicate small "") ++ ys ++ (replicate big "")
        correct = Calc $
          |~ small + (m + big)
          ~~ small + (big + m) ...(cong (small +) $ plusCommutative _ _)
          ~~(small + big) + m  ...(plusAssociative _ _ _)
          ~~ n + m             ...(cong (+ m) prf')
          ~~ height            ...(prf)
    in replace {p = \k => Vect k String} correct
       result

||| Input a vector of `n` strings, possibly containing new-lines
||| Output: One or more lines, reflowing each cell in the vector
|||   according to its newlines
|||
||| Example:
|||
|||   ["a\nb" , "cde", "f\n\g\n\h"]
|||
|||  becomes:
|||
|||  [["a"    , "cde", "f"]
|||  ,["b"    , ""   , "g"]
|||  ,[""     , ""   , "h"]
linesRow : (valignment : Vect n Vertical.Alignment) -> Vect n String -> List (Vect n String)
linesRow valignment xs =
    let xsLines = map lines xs
        heights = map List.length xsLines
        maximal = foldr max 0 heights
    in toList $ transpose $ zipWith (\v => valign v maximal) valignment xsLines

||| Print 1 row in the table,
printVect : (widths : Vect n Nat)
         -> (halignment : Vect n Horizontal.Alignment)
         -> Vect n String
         -> String
printVect widths halignment entries =
    pipeSeparate $ toList $
    zipWith3 (\algn,n,str => halign algn n str) halignment widths entries

formatTable : {n : Nat}
           -> (header : List (Vect n String))
           -> (body : SnocList (Vect n String))
           -> (halignment : Vect n Horizontal.Alignment)
           -> (valignment : Vect n Vertical.Alignment)
           -> String
formatTable header body halignment valignment =
    let header = foldMap (linesRow valignment) header
        rows   = foldMap (linesRow valignment) body
        maxWidths = foldr (\xs,acc => zipWith max (map length xs) acc)
                      (replicate _ 0) (rows ++ header)
    in unlines $ "" -- Empty first line makes printing alignment a little nicer
              :: (map (printVect maxWidths halignment) header)
              ++ (ruler $ toList maxWidths)
              :: (map (printVect maxWidths halignment) rows)

export
showTable : {schema : Schema}
         -> ShowSchema schema
         => {default (replicate (length schema) L) halignment : Vect (length schema) Horizontal.Alignment}
         -> {default (replicate (length schema) T) valignment : Vect (length schema) Vertical.Alignment}
         -> Table schema
         -> String
showTable table = formatTable {
    n = length schema,
    header = [nameVect schema],
    body = map showRecord table,
    halignment,
    valignment
  }

||| If we don't have access to the schema, we can still show the body
||| of the table.
export
showTableBody : (allShow : ShowSchema schema)
             => {default (replicate (length allShow) L) halignment : Vect (length allShow) Horizontal.Alignment}
             -> {default (replicate (length allShow) T) valignment : Vect (length allShow) Vertical.Alignment}
             -> Table schema
             -> String
-- Reconstruct the number of columns from the show instance :D
showTableBody table =
    let rows = replace {p = \n => SnocList (Vect n String)} (sym $ lengthAllLengthSchema allShow) $
               map showRecord table
    in formatTable {
        n = length allShow,
        header = [],
        body = rows,
        halignment,
        valignment
    }

export
{schema : Schema} -> ShowSchema schema => Show (Table schema) where
    show = showTable

export
showFrame : {schema : Schema}
         -> ShowSchema schema
         => {default (replicate (length schema) L) halignment : Vect (length schema) Horizontal.Alignment}
         -> {default (replicate (length schema) T) valignment : Vect (length schema) Vertical.Alignment}
         -> Frame schema n
         -> String
showFrame frm = showTable {halignment} {valignment} $ table frm

||| If we don't have access to the schema, we can still show the body
||| of the table.
export
showFrameBody : (allShow : ShowSchema schema)
             => {default (replicate (length allShow) L) halignment : Vect (length allShow) Horizontal.Alignment}
             -> {default (replicate (length allShow) T) valignment : Vect (length allShow) Vertical.Alignment}
             -> Frame schema n
             -> String
showFrameBody frm = showTableBody {halignment} {valignment} $ table frm
