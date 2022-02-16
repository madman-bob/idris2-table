module B2T2.TableAPI

import public Data.Table
import public Data.List

import B2T2.ExampleTables

%default total

public export
emptyTable : Table [<]
emptyTable = [<]
-- ensures:
--    schema(t) is equal to []
--    nrows(t) is equal to 0

public export
addRows :  (t1: Table schema)
        -> (rs: List (Record schema))
        -> Table schema
-- requires:
--    for all r in rs, schema(r) is equal to schema(t1)
addRows t1 [] = t1
addRows t1 (r :: rs) = addRows (t1 :< r) rs
-- ensures:
--    schema(t2) is equal to schema(t1)
--    nrows(t2) is equal to nrows(t1) + length(rs)

public export
addColumn :  (t1: Table schema)
          -> (0 c: String)
          -> (vs: SnocList type) -- TODO: -> (vs: List type)
          -> {auto 0 nRows : HasRows t1 (length vs)}
          -> Table (schema :< c :! type)
-- requires:
--    TODO: c is not in header(t1)
--    length(vs) is equal to nrows(t1)
addColumn t1 c vs = with Data.Table.Column.addColumn (addColumn c vs t1)
-- ensures:
--    header(t2) is equal to concat(header(t1), [c])
--    for all c' in header(t1), schema(t2)[c'] is equal to schema(t1)[c']
--    schema(t2)[c] is the sort of elements of vs
--    nrows(t2) is equal to nrows(t1)

public export
buildColumn :  (t1: Table schema)
            -> (0 c: String)
            -> (f: (Record schema -> type))
            -> Table (schema :< c :! type)
-- requires:
--    TODO: c is not in header(t1)
buildColumn t1 c f = with Data.Table.Column.buildColumn (buildColumn c f t1)
-- ensures:
--    schema(r) is equal to schema(t1)
--    header(t2) is equal to concat(header(t1), [c])
--    for all c' in header(t1), schema(t2)[c'] is equal to schema(t1)[c']
--    schema(t2)[c] is the sort of elements of vs
--    nrows(t2) is equal to nrows(t1)

public export
vcat : (t1: Table schema)
    -> (t2: Table schema)
    -> Table schema
-- requires:
--    schema(t1) is equal to schema(t2)
vcat t1 t2 = t1 ++ t2
-- ensures:
--    schema(t3) is equal to schema(t1)
--    nrows(t3) is equal to nrows(t1) + nrows(t2)

public export
hcat : (t1: Table schema1)
     -> (t2: Table schema2)
     -> Table (schema3) -- TODO: schema1 ++ schema2
-- requires:
--    TODO: concat(header(t1), header(t2)) has no duplicates
--    TODO: nrows(t1) is equal to nrows(t2)
hcat t1 t2 = ?hcat_t3
-- ensures:
--    schema(t3) is equal to concat(schema(t1), schema(t2))
--    nrows(t3) is equal to nrows(t1)

public export
values : (rs: SnocList (Record schema))
      -> Table schema
-- requires:
--    length(rs) is positive
--    for all r in rs, schema(r) is equal to schema(rs[0])
values [<] = [<]
values (rs :< r) = values rs :< r
-- ensures:
--    schema(t) is equal to schema(rs[0])
--    nrows(t) is equal to length(rs)

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
nrows : (t: Table schema) -> Nat
nrows [<] = Z
nrows (tbl :< rec) = S $ nrows tbl
-- ensures:
--    n is equal to nrows(t)

public export
ncols : (t: Table schema) -> Nat
ncols t = ?ncols_n
-- ensures:
--    n is equal to ncols(t)

public export
header : (t: Table schema) -> SnocList String
header t = ?header_cs -- with Data.Table.Schema.Data.names (names schema)
-- ensures:
--    cs is equal to header(t)

public export
getRow : (t: Table schema)
      -> (n: Nat)
      -> Record schema
-- requires:
--    n is in range(nrows(t))
getRow t n = ?getRow_r

public export
getValue : (r: Record schema)
        -> (c: String)
        -> type
-- requires:
--    c is in header(r)
getValue r c = ?getValue_v
-- ensures:
--    v is of sort schema(r)[c]

public export
getColumnByNumber :  (t: Table schema)
                  -> (n: Nat)
                  -> SnocList type
-- requires:
--    n is in range(ncols(t))
getColumnByNumber t n = ?getColumnByNumber_vs
-- ensures:
--    length(vs) is equal to nrows(t)
--    for all v in vs, v is of sort schema(t)[header(t)[n]]

public export
getColumnByName :  (t: Table schema)
                -> (c: String)
                -> SnocList type
-- requires:
--    c is in header(t)
getColumnByName t c = ?getColumnByName_vs
-- ensures:
--    for all v in vs, v is of sort schema(t)[c]
--    length(vs) is equal to nrows(t)

public export
selectRowsByNumber : (t1: Table schema)
                  -> (ns: List Nat)
                  -> Table schema
-- requires:
--    for all n in ns, n is in range(nrows(t1))
selectRowsByNumber t1 ns = ?selectRowsByNumber_t2
-- ensures:
--    schema(t2) is equal to schema(t1)
--    nrows(t2) is equal to length(ns)

public export
selectRowsByBoolean :  (t1: Table schema)
                    -> (bs: List Bool)
                    -> Table schema
-- requires:
--    length(bs) is equal to nrows(t1)
selectRowsByBoolean t1 bs = ?selectRowsByBoolean_t2
-- ensures:
--    schema(t2) is equal to schema(t1)
--    nrows(t2) is equal to length(removeAll(bs, [false]))

public export
selectColumnsByBoolean :  (t1: Table schema1)
                       -> (bs: List Bool)
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
                      -> (ns: List Nat)
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
head : (t1: Table schema)
    -> (n: Nat)
    -> Table schema
-- requires:
--    if n is non-negative then n is in range(nrows(t1))
--    if n is negative then - n is in range(nrows(t1))
head t1 n = ?head_t2
-- ensures:
--    schema(t2) is equal to schema(t1)
--    if n is non-negative then nrows(t2) is equal to n
--    if n is negative then nrows(t2) is equal to nrows(t1) + n

public export
distinct : (t1: Table schema)
        -> Table schema
distinct t1 = ?distinct_t2
-- ensures:
--    schema(t2) is equal to schema(t1)

public export
dropColumn : (t1: Table schema1)
          -> (c: String)
          -> Table schema2
-- requires:
--    c is in header(t1)
dropColumn t1 c = ?dropColumn_t2
-- ensures:
--    nrows(t2) is equal to nrows(t1)
--    header(t2) is equal to removeAll(header(t1), [c])
--    schema(t2) is a subsequence of schema(t1)

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
tfilter :  (t1: Table schema)
        -> (f: (Record schema -> Bool))
        -> Table schema
tfilter t1 f = ?tfilter_t2
-- ensures:
--    schema(r) is equal to schema(t1)
--    schema(t2) is equal to schema(t1)

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
update : (t1: Table schema1)
      -> (f: (Record schema1 -> Record schema2))
      -> Table schema2
-- requires:
--    for all c in header(r2), c is in header(t1)
-- ensures:
--    schema(r1) is equal to schema(t1)
--    header(t2) is equal to header(t1)
--    for all c in header(t2)
--      if c in header(r2) then schema(t2)[c] is equal to schema(r2)[c]
--      otherwise, schema(t2)[c] is equal to schema(t1)[c]
--    nrows(t2) is equal to nrows(t1)

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


