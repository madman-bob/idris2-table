module B2T2.TableAPI

import public Data.Table
import public Data.List
import public Data.Vect

import B2T2.ExampleTables

%default total

public export
||| Create an empty table
|||
||| emptyTable :: t.Table
|||   
||| requires:
|||   
||| ensures:
|||   - schema(t) is equal to []
|||   - nrows(t) is equal to 0
emptyTable : Table [<]
emptyTable = [<]

public export
||| Consumes a Table and a sequence of Row to add, and procudes a new Table with the rows from the
||| original table followed by the given Rows.
||| 
||| addRows :: t1:Table * rs:Seq<Row> -> t2:Table
|||
||| requires:
|||   - for all r in rs, schema(r) is equal to schema(t1) [Enforced by: Type]
|||
||| ensures:
|||   - schema(t2) is equal to schema(t1)
|||   - nrows(t2) is equal to nrows(t1) + length(rs)
addRows :  Table schema
        -> List (Record schema)
        -> Table schema
addRows t [] = t
addRows t (r :: rs) = addRows (t :< r) rs

addRows1: Table [<("name" :! String), ("age" :! Nat), ("favorite color" :! String)]
addRows1 = addRows students [ [<"Colton", 19, "blue"] ]

addRows2: Table [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Nat), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Nat)]
addRows2 = addRows gradebook []

public export
||| Consumes a column name and a Seq of values and produces a new Table with the columns of the input
||| Table followed by a column with the given name and values. Note that the length of vs must equal
||| the length of the Table.
|||
||| addColumn :: t1:Table * c:ColName * vs:Seq<Value> -> t2:Table
|||
||| requires:
|||   - c is not in header(t1)   [Enforced by: User]
|||   - length(vs) is equal to nrows(t1)  [Enforced by: Type]
|||
||| ensures:
|||   - header(t2) is equal to concat(header(t1), [c])
|||   - for all c' in header(t1), schema(t2)[c'] is equal to schema(t1)[c']
|||   - schema(t2)[c] is the sort of elements of vs
|||   - nrows(t2) is equal to nrows(t1)
addColumn :  (t: Table schema)
          -> (0 name: String)
          -> (values: SnocList type)
          -> {auto 0 nRows : HasRows t (length values)}
          -> Table (schema :< name :! type)
addColumn t name vs = Data.Table.Column.addColumn name vs t


addColumn1: Table [<("name" :! String), ("age" :! Nat), ("favorite color" :! String), ("hair-color" :! String)]
addColumn1 = addColumn students "hair-color" [<"brown", "red", "blonde"]

addColumn2: Table [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Nat), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Nat), ("presentation" :! Integer)]
addColumn2 = addColumn gradebook "presentation" [<9, 9, 6]

public export
||| Consumes an existing Table and produces a new Table containing an additional column with the
||| given ColName, using f to compute the values for that column, once for each row.
|||
||| buildColumn :: t1:Table * c:ColName * f:(r:Row -> v:Value) -> t2:Table
|||
||| requires:
|||   - c is not in header(t1)  [Enforced by: User]
|||
||| ensures:
|||   - schema(r) is equal to schema(t1)
|||   - header(t2) is equal to concat(header(t1), [c])
|||   - for all c' in header(t1), schema(t2)[c'] is equal to schema(t1)[c']
|||   - schema(t2)[c] is the sort of elements of vs
|||   - nrows(t2) is equal to nrows(t1)
buildColumn :  Table schema
            -> (0 name: String)
            -> (Record schema -> type)
            -> Table (schema :< name :! type)
buildColumn t name f = Data.Table.Column.buildColumn name f t

buildColumn1: Table [<("name" :! String), ("age" :! Nat), ("favorite color" :! String), ("is-teenager" :! Bool)]
buildColumn1 = buildColumn students "is-teenager" isTeenagerBuilder where
  isTeenagerBuilder : Record [<("name" :! String), ("age" :! Nat), ("favorite color" :! String)] -> Bool
  isTeenagerBuilder r = (12 < value "age" r) && (value "age" r < 20)
  -- isTeenagerBuilder r = (12 < (value "age" r)) and ((value "age" r) < 20) -- this throws a very hard to understand error ...

buildColumn2: Table [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Nat), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Nat), (?c :! Bool)]
buildColumn2 = buildColumn gradebook "did-well-in-final" didWellInFinal where
  didWellInFinal : Record [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Nat), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Nat)] -> Bool
  didWellInFinal r = 85 <= value "final" r

public export
||| Combines two tables vertically. The output table starts with rows from the first input table,
||| followed by the rows from the second input table.
|||
||| vcat :: t1:Table * t2:Table -> t3:Table
|||
||| requires:
|||   - schema(t1) is equal to schema(t2) [Enforced by: Type]
|||
||| ensures:
|||   - schema(t3) is equal to schema(t1)
|||   - nrows(t3) is equal to nrows(t1) + nrows(t2)
vcat : Table schema
    -> Table schema
    -> Table schema
vcat t1 t2 = t1 ++ t2

-- vcat1: ?t
-- vcat1 = vcat students (update students id)

{-
vcat1: Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
vcat1 = vcat students updatedStudents where
  updatedStudents : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
  updatedStudents = update students increaseAge
  increaseAge : Record [<"name" :! String, "age" :! Nat, "favorite color" :! String]
             -> Record [<"name" :! String, "age" :! Nat, "favorite color" :! String]
  increaseAge r = r
-}

public export
||| Combines two tables horizontally. The output table starts with columns from the first input,
||| followed by the columns from the second input.
|||
||| hcat :: t1:Table * t2:Table -> t3:Table
|||
||| requires:
|||   - concat(header(t1), header(t2)) has no duplicates  [Enforced by: User]
|||   - nrows(t1) is equal to nrows(t2) [Enforced by: Type]
|||
||| ensures:
|||   - schema(t3) is equal to concat(schema(t1), schema(t2))
|||   - nrows(t3) is equal to nrows(t1)
hcat : {n: Nat}
     -> (t1: Table schema1)
     -> {auto 0 t1HasRows : HasRows t1 n}
     -> (t2: Table schema2)
     -> {auto 0 t2HasRows : HasRows t2 n}
     -> Table (schema1 ++ schema2)
hcat {n = 0} [<] [<] = [<]
hcat {n = (S k)} {t1HasRows} (t1 :< rec1) {t2HasRows} (t2 :< rec2) =
  (hcat {n=k} {t1HasRows=dropRow t1HasRows} t1 {t2HasRows=dropRow t2HasRows} t2) :< (rec1 ++ rec2) where
    dropRow: HasRows (t :< _) (S m) -> HasRows t m
    dropRow (SnocTable hasRows) = hasRows

-- hcat1: ?t

public export
||| Returns a sequence of one or more rows as a table.
|||
||| requires:
|||   - length(rs) is positive  [Enforced by: Type]
|||   - for all r in rs, schema(r) is equal to schema(rs[0]) [Enforced by: Type]
|||
||| ensures:
|||   - schema(t) is equal to schema(rs[0])
|||   - nrows(t) is equal to length(rs)
values : SnocList (Record schema) -> Table schema
values [<] = [<]
values (rs :< r) = values rs :< r

public export
crossJoin :  (t1: Table schema1)
          -> (t2: Table schema2)
          -> Table schema
-- requires:
--    concat(header(t1), header(t2)) has no duplicates
crossJoin t1 t2 = ?crossJoin_t3
-- ensures:
--    schema(t3) is equal to concat(schema(t1), schema(t2))
--    nrows(t3) is equal to nrows(t1) * nrows(t2)

public export
leftJoin : (t1: Table schema1)
        -> (t2: Table schema2)
        -> (cs: List String)
        -> Table schema3
-- requires:
--    cs has no duplicates
--    for all c in cs, c is in header(t1)
--    for all c in cs, c is in header(t2)
--    for all c in cs, schema(t1)[c] is equal to schema(t2)[c]
--    concat(header(t1), removeAll(header(t2), cs)) has no duplicates
leftJoin t1 t2 cs = ?leftJoin_t3
-- ensures:
--    header(t3) is equal to concat(header(t1), removeAll(header(t2), cs))
--    for all c in header(t1), schema(t3)[c] is equal to schema(t1)[c]
--    for all c in removeAll(header(t2), cs)), schema(t3)[c] is equal to schema(t2)[c]
--    nrows(t3) is equal to nrows(t1)

public export
||| Returns a Number representing the number of rows in the Table.
|||
||| nrows :: t:Table -> n:Number
|||
||| ensures:
|||   n is equal to nrows(t)
nrows : Table schema -> Nat
nrows [<] = Z
nrows (tbl :< rec) = S $ nrows tbl

nrows1: Nat
nrows1 = nrows emptyTable

nrows2: Nat
nrows2 = nrows studentsMissing

public export
||| Returns a Number representing the number of columns in the Table.
|||
||| ncols :: t:Table -> n:Number
|||
||| ensures:
|||    n is equal to ncols(t)
ncols : {schema: Schema}
      -> Table schema
      -> Nat
ncols t = length schema

ncols1: Nat
ncols1 = ncols students

ncols2: Nat
ncols2 = ncols studentsMissing

public export
||| Returns a Seq representing the column names in the Table
|||
||| header :: t:Table -> cs:Seq<ColName>
|||
||| ensures:
|||    cs is equal to header(t)
header : {schema: Schema}
      -> Table schema
      -> SnocList String
header t = names schema

header1: SnocList String
header1 = header students

header2: SnocList String
header2 = header gradebook

public export
||| Extracts a row out of a table by a numeric index.
|||
||| getRow :: t:Table * n:Number -> r:Row
|||
||| requires:
|||   - n is in range(nrows(t)) [Enforced by: Type]
getRow : (t: Table schema)
      -> HasRows t n
      => Fin n
      -> Record schema
getRow = row

getRow1: Record [<("name" :! String), ("age" :! Nat), ("favorite color" :! String)]
getRow1 = getRow students 0

getRow2: Record [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Nat), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Nat)]
getRow2 = getRow gradebook 1

public export
||| Retrieves the value for the column c in the row r
|||
||| getValue :: r:Row * c:ColName -> v:Value
|||
||| requires:
|||   c is in header(r)
|||
||| ensures:
|||   v is of sort schema(r)[c]
getValue : Record schema
        -> (0 name: String)
        -> {auto field: Field schema name type}
        -> type
getValue r _ {field} = value field r

getValue1: String
getValue1 = getValue row "name" where
  row: Record [<"name" :! String, "age" :! Nat]
  row = [<"Bob", 12]

getValue2: Nat
getValue2 = getValue row "age" where
  row: Record [<"name" :! String, "age" :! Nat]
  row = [<"Bob", 12]

public export
||| Returns a Seq of the values in the indexed column in t
|||
||| getColumn :: t:Table * n:Number -> vs:Seq<Value>
|||
||| requires:
|||   n is in range(ncols(t)) [Enforced by: Type]
|||
||| ensures:
|||   length(vs) is equal to nrows(t)
|||   for all v in vs, v is of sort schema(t)[header(t)[n]]
getColumnByNumber : (t: Table schema)
                  -> (n: Fin (length schema))
                  -> SnocList type
getColumnByNumber t n = ?g
                  {-
getColumnByNumber t n = map (\r => indexValue (complement n) r) t where
  indexValue : {type: Type} -> {schema: Schema} -> Fin (length schema) -> Record schema -> type
  indexValue _ [<] impossible
  indexValue FZ (_ :< x) = x
  indexValue (FS y) (rec :< x) = indexValue y rec
  -}

public export
||| Returns a Seq of the values in the named column in t
||| 
||| getColumn :: t:Table * c:ColName -> vs:Seq<Value>
||| 
||| requires:
|||   c is in header(t) [Enforced by: Type]
||| 
||| ensures:
|||   for all v in vs, v is of sort schema(t)[c]
|||   length(vs) is equal to nrows(t)
getColumnByName :  Table schema
                -> (name: String)
                -> {auto field: Field schema name type}
                -> SnocList type
getColumnByName t _ {field} = column field t

getColumnByName1: SnocList Nat
getColumnByName1 = getColumnByName students "age"

getColumnByName2: SnocList String
getColumnByName2 = getColumnByName gradebook "name"

public export
||| Given a Table and a Seq<Number> containing row indices, produces a new Table containing only those rows.
|||
||| selectRows :: t1:Table * ns:Seq<Number> -> t2:Table
|||
||| requires:
|||    for all n in ns, n is in range(nrows(t1)) [Enforced by: Type]
|||
||| ensures:
|||    schema(t2) is equal to schema(t1)
|||    nrows(t2) is equal to length(ns)
selectRowsByNumber : (t: Table schema)
                  -> {n: Nat}
                  -> HasRows t n
                  => List (Fin n)
                  -> Table schema
selectRowsByNumber t is = selectRowsByNumberHelper t (reverse (map complement is)) where
  selectRowsByNumberHelper : (t: Table schema) -> {n: Nat} -> HasRows t n => List (Fin n) -> Table schema
  selectRowsByNumberHelper t [] = [<]
  selectRowsByNumberHelper t (i :: is) =
    let rest = selectRowsByNumberHelper t is in
        rest :< rowFromEnd t i

selectRowsByNumber1 : Table [<("name" :! String), ("age" :! Nat), ("favorite color" :! String)]
selectRowsByNumber1 = selectRowsByNumber students [2, 0, 2, 1]

selectRowsByNumber2 : Table [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Nat), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Nat)]
selectRowsByNumber2 = selectRowsByNumber gradebook [2, 1]

public export
||| Given a Table and a Seq<Boolean> that represents a predicate on rows,
||| returns a Table with only the rows for which the predicate returns true
|||
||| selectRows :: t1:Table * bs:Seq<Boolean> -> t2:Table
|||
||| requires:
|||    length(bs) is equal to nrows(t1) [Enforced by: Type]
|||
||| ensures:
|||    schema(t2) is equal to schema(t1)
|||    nrows(t2) is equal to length(removeAll(bs, [false]))
selectRowsByBoolean :  (t: Table schema)
                    -> {n: Nat}
                    -> HasRows t n
                    => Vect n Bool
                    -> Table schema
selectRowsByBoolean t bs = selectRowsByBooleanHelper t (reverse bs) where
  selectRowsByBooleanHelper : (t: Table schema) -> {n: Nat} -> HasRows t n => Vect n Bool -> Table schema
  selectRowsByBooleanHelper {n = 0} [<] [] = [<]
  selectRowsByBooleanHelper {n = _} @{SnocTable _} (tbl :< rec) (b :: bs) =
    let rest = selectRowsByBooleanHelper tbl bs in
        case b of
             False => rest
             True => rest :< rec

selectRowsByBoolean1 : Table [<("name" :! String), ("age" :! Nat), ("favorite color" :! String)]
selectRowsByBoolean1 = selectRowsByBoolean students [True, False, True]

selectRowsByBoolean2 : Table [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Nat), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Nat)]
selectRowsByBoolean2 = selectRowsByBoolean gradebook [False, False, True]

public export
selectColumnsByBoolean :  (t1: Table schema1)
                       -> (bs: Vect (length schema1) Bool)
                       -> Table schema2
-- requires:
--    length(bs) is equal to ncols(t1)
selectColumnsByBoolean t1 bs = ?selectColumnsByBoolean_t2
-- ensures:
--    header(t2) is a subsequence of header(t1)
--    for all i in range(ncols(t1)), header(t1)[i] is in header(t2) if and only if bs[i] is equal to true
--    schema(t2) is a subsequence of schema(t1)
--    nrows(t2) is equal to nrows(t1)

public export
selectColumnsByNumber :  (t1: Table schema1)
                      -> (ns: List (Fin (length schema1)))
                      -> Table schema2
-- requires:
--    ns has no duplicates
--    for all n in ns, n is in range(ncols(t1))
selectColumnsByNumber t1 ns = ?selectColumnsByNumber_t2
-- ensures:
--    ncols(t2) is equal to length(ns)
--    for all i in range(length(ns)), header(t2)[i] is equal to header(t1)[ns[i]]
--    for all c in header(t2), schema(t2)[c] is equal to schema(t1)[c]
--    nrows(t2) is equal to nrows(t1)

public export
selectColumnsByName :  (t1: Table schema1)
                    -> (cs: List String)
                    -> Table schema2
-- requires:
--    cs has no duplicates
--    for all c in cs, c is in header(t1)
selectColumnsByName t1 cs = ?selectColumnsByName_t2
-- ensures:
--    header(t2) is equal to cs
--    for all c in header(t2), schema(t2)[c] is equal to schema(t1)[c]
--    nrows(t2) is equal to nrows(t1)

public export
||| Returns the first n rows of the table based on position.
||| TODO: support for negative values
||| For negative values of n, this function returns all rows except the last n rows.
|||
||| head :: t1:Table * n:Number -> t2:Table
|||
||| requires:
|||    if n is non-negative then n is in range(nrows(t1))
|||    if n is negative then - n is in range(nrows(t1))
|||
||| ensures:
|||    schema(t2) is equal to schema(t1)
|||    if n is non-negative then nrows(t2) is equal to n
|||    if n is negative then nrows(t2) is equal to nrows(t1) + n
head : (t: Table schema)
    -> {n: Nat}
    -> HasRows t n
    => Fin (S n)
    -> Table schema
head t n = dropRows t (complement n)

head1 : Table [<("name" :! String), ("age" :! Nat), ("favorite color" :! String)]
head1 = head students 1

public export
distinct : (t1: Table schema)
        -> Table schema
distinct t1 = ?distinct_t2
-- ensures:
--    schema(t2) is equal to schema(t1)

public export
||| Returns a Table that is the same as t, except without the named column
|||
||| dropColumn :: t1:Table * c:ColName -> t2:Table
|||
||| requires:
|||    c is in header(t1)
|||
||| ensures:
|||   nrows(t2) is equal to nrows(t1)
|||    header(t2) is equal to removeAll(header(t1), [c])
|||    schema(t2) is a subsequence of schema(t1)
dropColumn : Table schema
          -> (name: String)
          -> {field: Field schema name type}
          -> Table (drop schema field)
dropColumn t _ {field} = Data.Table.Column.dropColumn field t

public export
dropColumns :  (t1: Table schema1)
            -> (cs: List String)
            -> Table schema2
-- requires:
--    for all c in cs, c is in header(t1)
--    cs has no duplicates
dropColumns t1 c2 = ?dropColumns_t2
-- ensures:
--    nrows(t2) is equal to nrows(t1)
--    header(t2) is equal to removeAll(header(t1), cs)
--    schema(t2) is a subsequence of schema(t1)

public export
||| Given a Table and a predicate on rows, returns a Table with only the rows for which the predicate returns true
|||
||| tfilter :: t1:Table * f:(r:Row -> b:Boolean) -> t2:Table
|||
||| ensures:
|||    schema(r) is equal to schema(t1)
|||    schema(t2) is equal to schema(t1)
tfilter :  Table schema
        -> (Record schema -> Bool)
        -> Table schema
tfilter t f = filter f t

tfilter1 : Table [<("name" :! String), ("age" :! Nat), ("favorite color" :! String)]
tfilter1 = tfilter students (\r => (value "age" r) < 15)

tfilter2 : Table [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Nat), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Nat)]
tfilter2 = tfilter gradebook (\r => (length (value "name" r)) > 3)

public export
tsort :  (t1: Table schema)
      -> (c: String)
      -> (b: Bool)
      -> Table schema
-- requires:
--    c is in header(t1)
--    schema(t1)[c] is Number
tsort t1 c b = ?tsort_t2
-- ensures:
--    nrows(t2) is equal to nrows(t1)
--    schema(t2) is equal to schema(t1)

public export
sortByColumns :  (t1: Table schema)
              -> (cs: List String)
              -> Table schema
-- requires:
--    cs has no duplicates
--    for all c in cs, c is in header(t1)
--    for all c in cs, schema(t1)[c] is Number
sortByColumns t1 cs = ?sortByColumns_t2
-- ensures:
--    nrows(t2) is equal to nrows(t1)
--    schema(t2) is equal to schema(t1)

public export
orderBy :  (t1: Table schema)
        -> List (k: Type ** (Record schema -> k, k -> k -> Bool))
        -> Table schema
orderBy t1 fs = ?orderBy_t2
-- ensures:
--    schema(r) is equal to schema(t1)
--    schema(t2) is equal to schema(t1)
--    nrows(t2) is equal to nrows(t1)

public export
count :  (t1: Table schema)
      -> (c: String)
      -> Table schema
-- requires:
--    c is in header(t1)
--    schema(t1)[c] is a categorical sort
count t1 c = ?count_t2
-- ensures:
--    header(t2) is equal to ["value", "count"]
--    schema(t2)["value"] is equal to schema(t1)[c]
--    schema(t2)["count"] is equal to Number
--    nrows(t2) is equal to length(removeDuplicates(getColumn(t1, c)))

public export
bin :  (t1: Table schema1)
    -> (c: String)
    -> (n: Nat)
    -> Table schema2
-- requires:
--    c is in header(t1)
--    schema(t1)[c] is Number
bin t1 c n = ?bin_t2
-- ensures:
--    header(t2) is equal to ["group", "count"]
--    schema(t2)["group"] is String
--    schema(t2)["count"] is Number

public export
pivotTable : (t1: Table schema1)
          -> (cs: List String)
          -> (aggs: List (String, String, ?function))
          -> Table schema2
-- constraints:
--    Let ci1 and ci2 and fi be the components of aggs[i] for all i in range(length(aggs))
-- requires:
--    for all c in cs, c is in header(t1)
--    for all c in cs, schema(t1)[c] is a categorical sort
--    ci2 is in header(t1)
--    concat(cs, [c11, ... , cn1]) has no duplicates
-- ensures:
--    fi consumes Seq<schema(t1)[ci2]>
--    header(t2) is equal to concat(cs, [c11, ... , cn1])
--    for all c in cs, schema(t2)[c] is equal to schema(t1)[c]
--    schema(t2)[ci1] is equal to the sort of outputs of fi for all i

public export
groupBy :  (t1: Table schema1)
        -> (key: (Record schema1 -> k))
        -> (project: (Record schema1 -> v))
        -> (aggregate: ((k, List v) -> Record schema2))
        -> Table schema2
-- ensures:
--    schema(r1) is equal to schema(t1)
--    schema(r2) is equal to schema(t1)
--    schema(t2) is equal to schema(r3)
--    nrows(t2) is equal to length(removeDuplicates(ks)), where ks is the results of applying key to each row of t1. ks can be defined with select and getColumn

public export
completeCases :  (t: Table schema)
              -> (c: String)
              -> List Bool
-- requires:
--    c is in header(t)
-- ensures:
--    length(bs) is equal to nrows(t)

public export
dropna : (t1: Table schema)
      -> Table schema
-- ensures:
--    schema(t2) is equal to schema(t1)

public export
fillna : (t1: Table schema)
      -> (c: String)
      -> (v: type)
      -> Table schema
-- requires:
--    c is in header(t1)
--    v is of sort schema(t1)[c]
-- ensures:
--    schema(t2) is equal to schema(t1)
--    nrows(t2) is equal to nrows(t1)

public export
pivotLonger :  (t1: Table schema1)
            -> (cs: List String)
            -> (c1: String)
            -> (c2: String)
            -> Table schema2
-- requires:
--    length(cs) is positive
--    cs has no duplicates
--    for all c in cs, c is in header(t1)
--    for all c in cs, schema(t1)[c] is equal to schema(t1)[cs[0]]
--    concat(removeAll(header(t1), cs), [c1, c2]) has no duplicates
-- ensures:
--    header(t2) is equal to concat(removeAll(header(t1), cs), [c1, c2])
--    for all c in removeAll(header(t1), cs), schema(t2)[c] is equal to schema(t1)[c]
--    schema(t2)[c1] is equal to ColName
--    schema(t2)[c2] is equal to schema(t1)[cs[0]]

public export
pivotWider : (t1: Table schema1)
          -> (c1: String)
          -> (c2: String)
          -> Table schema2
-- requires:
--    c1 is in header(t1)
--    c2 is in header(t1)
--    schema(t1)[c1] is ColName
--    concat(removeAll(header(t1), [c1, c2]), removeDuplicates(getColumn(t1, c1))) has no duplicates
-- ensures:
--    header(t2) is equal to concat(removeAll(header(t1), [c1, c2]), removeDuplicates(getColumn(t1, c1)))
--    for all c in removeAll(header(t1), [c1, c2]), schema(t2)[c] is equal to schema(t1)[c]
--    for all c in removeDuplicates(getColumn(t1, c1)), schema(t2)[c] is equal to schema(t1)[c2]

public export
flatten :  (t1: Table schema1)
        -> (cs: List String)
        -> Table schema2
-- requires:
--    cs has no duplicates
--    for all c in cs, c is in header(t1)
--    for all c in cs, schema(t1)[c] is Seq<X> for some sort X
--    for all i in range(nrows(t1)), for all c1 and c2 in cs, length(getValue(getRow(t1, i), c1)) is equal to length(getValue(getRow(t1, i), c2))
-- ensures:
--    header(t2) is equal to header(t1)
--    for all c in header(t2)
--      if c is in cs then schema(t2)[c] is equal to the element sort of schema(t1)[c]
--      otherwise, schema(t2)[c] is equal to schema(t1)[c]

public export
transformColumn :  (t1: Table schema1)
                -> (c: String)
                -> (f: (type -> type))
                -> Table schema2
-- requires:
--    c is in header(t1)
-- ensures:
--    v1 is of sort schema(t1)[c]
--    header(t2) is equal to header(t1)
--    for all c' in header(t2)
--      if c' is equal to c then schema(t2)[c'] is equal to the sort of v2
--      otherwise, then schema(t2)[c'] is equal to schema(t1)[c']
--    nrows(t2) is equal to nrows(t1)

public export
renameColumns :  (t1: Table schema1)
              -> (ccs: List (String, String))
              -> Table schema2
-- constraints:
--    Let n be the length of ccs Let c11 ... c1n be the first components of the elements of ccs and c21 ... c2n be the second components.
-- requires:
--    c1i is in header(t1) for all i
--    [c11 ... c1n] has no duplicates
--    concat(removeAll(header(t1), [c11 ... c1n]), [c21 ... c2n]) has no duplicates
-- ensures:
--    header(t2) is equal to header(t1) with all c1i replaced with c2i
--    for all c in header(t2)
--      if c is equal to c2i for some i then schema(t2)[c2i] is equal to schema(t1)[c1i]
--      otherwise, schema(t2)[c] is equal to schema(t2)[c]
--    nrows(t2) is equal to nrows(t1)

public export
find : (t: Table schema)
    -> (r: Record schema)
    -> Maybe Nat
-- requires:
--    for all c in header(r), c is in header(t)
--    for all c in header(r), schema(r)[c] is equal to schema(t)[c]
-- ensures:
--    either n is equal to error("not found") or n is in range(nrows(t))

public export
groupByRetentive : (t1: Table schema1)
                -> (c: String)
                -> Table schema2
-- requires:
--    c is in header(t1)
--    schema(t1)[c] is a categorical sort
-- ensures:
--    header(t2) is equal to ["key", "groups"]
--    schema(t2)["key"] is equal to schema(t1)[c]
--    schema(t2)["groups"] is Table
--    getColumn(t2, "key") has no duplicates
--    for all t in getColumn(t2, "groups"), schema(t) is equal to schema(t1)
--    nrows(t2) is equal to length(removeDuplicates(getColumn(t1, c)))

public export
groupBySubstractive :  (t1: Table schema1)
                    -> (c: String)
                    -> Table schema2
-- requires:
--    c is in header(t1)
--    schema(t1)[c] is a categorical sort
-- ensures:
--    header(t2) is equal to ["key", "groups"]
--    schema(t2)["key"] is equal to schema(t1)[c]
--    schema(t2)["groups"] is Table
--    getColumn(t2, "key") has no duplicates
--    for all t in getColumn(t2, "groups"), header(t) is equal to removeAll(header(t1), [c])
--    for all t in getColumn(t2, "groups"), schema(t) is a subsequence of schema(t1)
--    nrows(t2) is equal to length(removeDuplicates(getColumn(t1, c)))

public export
||| Consumes an existing Table and produces a new Table with the named columns updated,
||| using f to produce the values for those columns, once for each row.
||| TODO: match B2T2 API
|||
||| update :: t1:Table * f:(r1:Row -> r2:Row) -> t2:Table
|||
||| requires:
|||   for all c in header(r2), c is in header(t1) [Enforced by: User]
|||
||| ensures:
|||    schema(r1) is equal to schema(t1)
|||    header(t2) is equal to header(t1)
|||    for all c in header(t2)
|||      if c in header(r2) then schema(t2)[c] is equal to schema(r2)[c]
|||      otherwise, schema(t2)[c] is equal to schema(t1)[c]
|||    nrows(t2) is equal to nrows(t1)
update : Table schema
      -> (Record schema -> Record schema2)
      -> Table schema2
update t f = toTable (map f t) where
  toTable : SnocList (Record s) -> Table s
  toTable [<] = [<]
  toTable (lst :< rec) = toTable lst :< rec

update1 : Table [<("name" :! String), ("age" :! String), ("favorite color" :! String)]
update1 = update students abstractAge where
  abstractAge : Record [<"name" :! String, "age" :! Nat, "favorite color" :! String]
             -> Record [<"name" :! String, "age" :! String, "favorite color" :! String]
  abstractAge r = updateField "age" (\age => if age <= 12 then "kid"
                                             else if age <= 19 then "teenager"
                                             else "adult") r

update2: Table [<("name" :! String), ("age" :! Nat), ("quiz1" :! Nat), ("quiz2" :! Nat), ("midterm" :! Bool), ("quiz3" :! Nat), ("quiz4" :! Nat), ("final" :! Bool)]
update2 = update gradebook didWellInFinal where
  didWellInFinal : Record [< "name" :! String, "age" :! Nat, "quiz1" :! Nat, "quiz2" :! Nat,
                             "midterm" :! Nat, "quiz3" :! Nat, "quiz4" :! Nat, "final" :! Nat ]
                -> Record [< "name" :! String, "age" :! Nat, "quiz1" :! Nat, "quiz2" :! Nat,
                             "midterm" :! Bool, "quiz3" :! Nat, "quiz4" :! Nat, "final" :! Bool ]
  didWellInFinal r = let r1 = updateField "midterm" (\grade => 85 <= grade) r in
                         updateField "final" (\grade => 85 <= grade) r1


public export
select : (t1: Table schema1)
      -> (f: ((Record schema1, Nat) -> Record schema2))
      -> Table schema2
-- ensures:
--    schema(r1) is equal to schema(t1)
--    n is in range(nrows(t1))
--    schema(t2) is equal to schema(r2)
--    nrows(t2) is equal to nrows(t1)

public export
selectMany : (t1: Table schema1)
          -> (project: ((Record schema1, Nat) -> Table schema2))
          -> (result: (Record schema1, Record schema2) -> Record schema2)
          -> Table schema2
-- ensures:
--    schema(r1) is equal to schema(t1)
--    n is in range(nrows(t1))
--    schema(r2) is equal to schema(t1)
--    schema(r3) is equal to schema(t2)
--    schema(t2) is equal to schema(r4)

public export
groupJoin :  (t1: Table schema1)
          -> (t2: Table schema2)
          -> (getKey1: (Record schema1 -> k))
          -> (getKey2: (Record schema2 -> k))
          -> (aggregate: ((Record schema1, Table schema2) -> Record schema3))
          -> Table schema3
-- ensures:
--    schema(r1) is equal to schema(t1)
--    schema(r2) is equal to schema(t2)
--    schema(r3) is equal to schema(t1)
--    schema(t3) is equal to schema(t2)
--    schema(t4) is equal to schema(r4)
--    nrows(t4) is equal to nrows(t1)

public export
join : (t1: Table schema1)
    -> (t2: Table schema2)
    -> (getKey1: (Record schema1 -> k))
    -> (getKey2: (Record schema2 -> k))
    -> (combine: ((Record schema1, Record schema2) -> Record schema3))
    -> Table schema3
-- ensures:
--    schema(r1) is equal to schema(t1)
--    schema(r2) is equal to schema(t2)
--    schema(r3) is equal to schema(t1)
--    schema(r4) is equal to schema(t2)
--    schema(t3) is equal to schema(r5)


