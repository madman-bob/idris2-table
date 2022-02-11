module Data.Table.Row.Frame

import public Data.DPair

import public Data.Table.Data
import public Data.Table.Row.HasRows

%default total

public export
Frame : Schema -> Nat -> Type
Frame schema n = Subset (Table schema) (`HasRows` n)

public export
Lin : Frame schema 0
Lin = Element [<] EmptyTable

public export
(:<) : Frame schema n -> Record schema -> Frame schema (S n)
(Element tbl hasRows) :< row = Element (tbl :< row) (SnocTable hasRows)

public export
%inline
init : Frame schema (S n) -> Frame schema n
init = uncurry go
  where
    go : (tbl : Table schema) -> (0 hasRows : HasRows tbl (S n)) -> Frame schema n
    go (tbl :< _) (SnocTable hasRows) = Element tbl hasRows

public export
%inline
last : Frame schema (S n) -> Record schema
last (Element (tbl :< row) hasRows) = row

public export
%inline
frame : (tbl : Table schema)
     -> {auto 0 hasRows : HasRows tbl n}
     -> Frame schema n
frame tbl = Element tbl hasRows

public export
%inline
table : (frm : Frame schema n)
     -> Table schema
table (Element tbl hasRows) = tbl

public export
%hint
0
frameHasRows : (frm : Frame schema n)
            -> {0 tbl : _}
            -> {auto 0 ford : tbl = table frm}
            -> HasRows tbl n
frameHasRows {ford = Refl} (Element tbl hasRows) = hasRows

public export
(|+|) : Frame schema1 n -> Frame schema2 n -> Frame (schema1 ++ schema2) n
frame1 |+| frame2 =
  -- hint we want to use these
  let 0 nrows1 = frame1.snd
      0 nrows2 = frame2.snd in
  frame1.fst |+| frame2.fst
    `Element`
  hConcatHasRows frame1.fst frame2.fst
