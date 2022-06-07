## Reference

> Q. What is the URL of the version of the benchmark being used?

https://github.com/brownplt/B2T2/tree/v1.0

> Q. On what date was this version of the datasheet last updated?

2022-06-07

> Q. If you are not using the latest benchmark available on that date, please explain why not.

N/A

## Example Tables

Sample implementations of all the B2T2 Example Tables may be found in [B2T2/ExampleTables.idr](B2T2/ExampleTables.idr).

> Q. Do tables express heterogeneous data, or must data be homogenized?

Tables can express heterogeneous data. Each column may be any Idris 2 type.

For example:

```idris
Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
```

This is the type for a table with three columns, called `"name"`, `"age"`, and `"favorite color"`.
The types of these columns are `String`, `Nat`, and `String`, respectively.

> Q. Do tables capture missing data and, if so, how?

Columns may use the `Maybe` type to allow missing data.
As this is a per-column constraint, programmers may indicate which columns allow missing data.

This enforces handling of potentially missing values, with no extra complexity for required values.

For example, in a table of type:

```idris
Table [<"name" :! String, "age" :! Maybe Nat, "favorite color" :! Maybe String]
```

The column `"name"` is required, while `"age"` and `"favorite color"` may be missing.

> Q. Are mutable tables supported? Are there any limitations?

All objects in Idris 2 are immutable, so mutable tables are not supported.

Standard functional programming idioms can be used to imitate mutation.
With the right optimizations, these idioms will even be compiled down to the use of mutation.
These idioms then enforce correctness even if the schema of a table changes over its lifetime.

> You may reference, instead of duplicating, the responses to the above questions in answering those below:

> Q. Which tables are inexpressible? Why?

All the B2T2 Example Tables may be fully expressed.

> Q. Which tables are only partially expressible? Why, and what’s missing?

All the B2T2 Example Tables may be fully expressed.

We do not support types of columns to depend on the values in other columns (called "dependant-column tables", as opposed to "simple-column tables").

For example:

```lua
| name    | age | quizzes completed | quizzes      | midterm | final |
| ------- | --- | ----------------- | ------------ | ------- | ----- |
| "Bob"   | 12  | 4                 | [8, 9, 7, 9] | 77      | 87    |
| "Alice" | 17  | 3                 | [6, 8, 7]    | 88      | 85    |
| "Eve"   | 13  | 3                 | [9, 8, 8]    | 84      | 77    |
```

We cannot express, in the table type, that the length of `quizzes`, is equal to the value in `quizzes completed`.
However, this may be expressed by the use of an additional proof type.

In the above example, if we encode `quizzes` as a `List Nat`, in a `Table` called `tbl`, then we can encode this column dependency as the following proof type on `tbl`:

```idris
AllRows (\rec => value "quizzes completed" rec = length (value "quizzes" rec)) tbl
```

More generally, for arbitrary indexed types, we can use the `Exists` type.
In the above example, we could do this by instead encoding `quizzes` as an `Exists (\n => Vect n Nat)`.
That is, there is some length `n`, such that `quizzes` is a list of that length.
We can then link the columns together with the following proof type:

```idris
AllRows (\rec => value "quizzes completed" rec = fst (value "quizzes" rec)) tbl
```

> Q. Which tables’ expressibility is unknown? Why?

All simple-column tables are expressible.
All dependant-column tables are indirectly expressible, through the use of the `AllRows` type, as in the previous question.

> Q. Which tables can be expressed more precisely than in the benchmark? How?

In the `gradebookSeq` example, we may state the type of the `"quizzes"` column to be either `List Nat`, or `Vect 4 Nat`.
Using `Vect 4 Nat` says that all students must have completed exactly four exams.
For `List Nat`, we are instead saying that students may have different numbers of quiz results (perhaps some students may have missed some exams).

For example, the following table could be expressed by the `quizzes` column being of type `List Nat`, but not `Vect 4 Nat`.

```lua
| name    | age | quizzes      | midterm | final |
| ------- | --- | ------------ | ------- | ----- |
| "Bob"   | 12  | [8, 9, 7, 9] | 77      | 87    |
| "Alice" | 17  | [6, 8, 7]    | 88      | 85    |
| "Eve"   | 13  | [9, 8, 8]    | 84      | 77    |
```

> Q. How direct is the mapping from the tables in the benchmark to representations in your system? How complex is the encoding?

The B2T2 example tables map directly to `Table`s in our library.

The names of columns may be any Idris 2 `String`, and the types may be any Idris 2 `Type`.
Further, tables may be written using Idris 2's `SnocList` notation, for convenience of `Table` literals.

For example:

```idris
students : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
students = [<
    [<"Bob",   12, "blue" ],
    [<"Alice", 17, "green"],
    [<"Eve",   13, "red"  ]
  ]
```

is an encoding of the table

```lua
| name    | age | favorite color |
| ------- | --- | -------------- |
| "Bob"   | 12  | "blue"         |
| "Alice" | 17  | "green"        |
| "Eve"   | 13  | "red"          |
```

## TableAPI

> Q. Are there consistent changes made to the way the operations are represented?

Operations are encoded as Idris 2 functions.

Both "requires" and "ensures" constraints of an operation are encoded in the type of the function, where possible.
Some constraints are encoded as additional proof objects about the function.

> Q. Which operations are entirely inexpressible? Why?

All B2T2 Table API operations are expressible.

> Q. Which operations are only partially expressible? Why, and what’s missing?

For simplicity, we chose not to enforce uniqueness of column names.
While possible to encode in Idris 2, the proofs relating to uniqueness are quite fiddly.
Further, this requirement does not provide much benefit, as Idris 2 proof inference can help disambiguate.

For example, with a table `tbl` of type:

```idris
Table [<"x" :! Nat, "x" :! String]
```

If we call `column "x" tbl` in a context that requires a `Nat` column, then Idris 2 will infer that we meant the first column.
Similarly, if we call `column "x" tbl` in a context that requires a `String` column, then Idris 2 will infer that we meant the second column.

On the other hand, if we call `column "x" tbl` in a context where either would work, then this will be a compile-time error, due to ambiguity.
In this case, we can refer to the column instead by index, or disambiguate manually, by constructing the appropriate proof object.

> Q. Which operations’ expressibility is unknown? Why?

All B2T2 Table API operations are expressible.

> Q. Which operations can be expressed more precisely than in the benchmark? How?

We allow `emptyTable` to have any schema (including the empty schema).
It is often useful to have an empty table of any particular schema.

For example, both

```lua
| name | age | favorite color |
| ---- | --- | -------------- |
```

and

```lua
| name | age | quizzes | midterm | final |
| ---- | --- | ------- | ------- | ----- |
```

are empty tables, but have different, non-empty, schemas.

As an example of where this is useful, we can define

```
values(rs) = addRows(emptyTable, rs)
```

to convert a sequence of rows into a table.
This requires that the `emptyTable` have the same schema as all the given rows.

Further, our version of `values` does not require that `rs` is non-empty.
Instead, we get the schema of the resultant table from the type of the sequence passed in.

The operations that handle missing values, we restrict to only those columns that allow missing values.

## Example Programs

Sample implementations of all the B2T2 Example Programs may be found in [B2T2/ExamplePrograms](B2T2/ExamplePrograms).

> Q. Which examples are inexpressible? Why?

All B2T2 Example Programs are expressible.

> Q. Which examples’ expressibility is unknown? Why?

All B2T2 Example Programs are expressible.

> Q. Which examples, or aspects thereof, can be expressed especially precisely? How?

All the sample implementations use dependent types to enforce constraints at compile-time.

The [`dotProduct`](B2T2/ExamplePrograms/DotProduct.idr) example has type-signature:

```idris
dot : Num a
   => Field schema c1 a
   -> Field schema c2 a
   -> Table schema
   -> a
```

We enforce that the two used columns, and the result, are of the same type by repeated use of `a` in the type-signature.
Further, we enforce that `a` is numeric by the constraint `Num a`.

The [`sampleRows`](B2T2/ExamplePrograms/SampleRows.idr) example has type-signature:

```idris
sampleRows : HasIO io
          => {n : Nat}
          -> (frm : Frame schema n)
          -> (k : Fin (S n))
          -> io (Frame schema (cast k))
```

We use the terminology that a `Frame schema n` is a `Table schema`, with precisely `n` rows.

This function samples `k` rows from a table with `n` rows.
We enforce that `k <= n`, by making `k` of type `Fin (S n)`.
Further, we enforce that the resultant table has exactly `k` rows, as this table is a `Frame schema (cast k)`.

The computation is done in an `io` monad, to handle randomness.

The [`pHacking`](B2T2/ExamplePrograms/PHacking.idr) examples have type-signature:

```idris
pHacking : {schema : Schema}
        -> (0 _ : AllColumns schema Bool)
        => {baseCol : String}
        -> Field schema baseCol Bool
        -> Table schema
        -> IO ()
```

The constraint `AllColumns schema Bool` enforces all columns of the `schema` to be `Bool`s.

The Idris 2 type-system is powerful enough to handle the `pHackingHeterogeneous` example with no further programmer code.

That is, the following type-checks:

```idris
pHacking "get acne" $ dropColumn "name" jellyNamed
```

The [`quizScoreFilter`](B2T2/ExamplePrograms/QuizScoreFilter.idr) example, uses the custom proof types:

```idris
data GradebookColumn : (fs : FieldSchema) -> Type -> Type where [search fs]
    QuizCol : So (isPrefixOf "quiz" name) -> GradebookColumn (name :! a) a
    NoQuizCol : So (not $ isPrefixOf "quiz" name) -> GradebookColumn (name :! type) a

GradebookSchema : Schema -> Type -> Type
GradebookSchema schema a = All (`GradebookColumn` a) schema
```

The `GradebookSchema schema a` type enforces that all columns in `schema` whose names begin with `"quiz"` are of type `a`.
This is how we explain the link between column names and types to the compiler.
We use this for type-safe iteration over the columns of "gradebook" tables.

The [`quizScoreSelect`](B2T2/ExamplePrograms/QuizScoreSelect.idr) example, uses the custom proof type:

```idris
data HasQuizzes : (schema : Schema) -> (n : Nat) -> (a : Type) -> Type where [search schema n]
    Lin : HasQuizzes schema 0 a
    (:<) : HasQuizzes schema n a -> Field schema ("quiz" ++ cast (S n)) a -> HasQuizzes schema (S n) a
```

Similarly to the `quizScoreFilter` example, the `HasQuizzes schema n a` type proves that `schema` has at least `n` `"quiz"` columns, of type `a`.
This is how we explain the link between column names and types to the compiler.
We use this for type-safe selection of our `"quiz"` columns.

The [`groupBy`](B2T2/ExamplePrograms/GroupBy.idr) examples are based off a single function, of type-signature:

```idris
groupByGeneral : Field schema keyCol a
              -> Ord a
              => (Record schema -> Record groupSchema)
              -> Table schema
              -> Table [<"key" :! a, "groups" :! Table groupSchema]
```

We specialize on the argument that takes a function.
For `groupByRetentive`, we pass in `id`, the identity function.
For `groupBySubtractive`, we pass in `dropField keyFld`, to drop the key column.

These versions of `groupBy` also match the constraints defined in the Table API.

> Q. How direct is the mapping from the pseudocode in the benchmark to representations in your system? How complex is the encoding?

Most of the examples would be written differently to how they are written in the B2T2 Example Programs, to work naturally in Idris 2.
While it is possible to write these functions in the style presented in the Example Programs, we would also need a number of auxiliary lemmas to prove correctness.
Our implementations are idiomatic approaches to these problems in Idris 2, where correctness is proved by construction.
A programmer familiar with Idris 2 would instinctively write these functions in a similar style.

The `dotProduct` example was expressed recursively, in the standard functional style.

The `sampleRows` example was the most fiddly, requiring use of the Idris 2 built-in `replace` function to prove that the resultant table had the right number of rows.
This example was also expressed recursively, as it was written without a built-in `sample` on lists available.

The `pHacking` examples were written without pulling the columns into separate variables, to avoid having to prove that they are the same length.

The `quizScoreFilter` example constructed an additional proof-type to iterate over the columns in a type-safe way, rather than use `filter`.

The `quizScoreSelect` example constructed an additional proof-type to select the columns in a type-safe way, rather than use `map`.

The `groupBy` examples were written with the Idris 2 `SortedMap` type, for simplicity.

## Errors

Sample implementations of all the B2T2 example Errors may be found in [B2T2/Errors](B2T2/Errors).

These implementations use the Idris 2 `failing` block, which type-checks only when its contents does *not* type-check.
We do this to ensure that these errors are caught by the type-checker.

> There are (at least) two parts to errors: representing the source program that causes the error, and generating output that explains it. The term “error situation” refers to a representation of the cause of the error in the program source.
>
> For each error situation it may be that the language:
>
> - isn’t expressive enough to capture it
> - can at least partially express the situation
> - prevents the program from being constructed
>
> Expressiveness, in turn, can be for multiple artifacts:
>
> - the buggy versions of the programs
> - the correct variants of the programs
> - the type system’s representation of the constraints
> - the type system’s reporting of the violation

> Q. Which error situations are known to be inexpressible? Why?

All B2T2 example Errors are expressible syntactically in Idris 2.

All B2T2 example Error buggy programs are rejected by the Idris 2 type-checker.

> Q. Which error situations are only partially expressible? Why, and what’s missing?

All B2T2 example Errors are expressible syntactically in Idris 2.

All B2T2 example Error buggy programs are rejected by the Idris 2 type-checker.

> Q. Which error situations’ expressibility is unknown? Why?

All B2T2 example Errors are expressible syntactically in Idris 2.

All B2T2 example Error buggy programs are rejected by the Idris 2 type-checker.

> Q. Which error situations can be expressed more precisely than in the benchmark? How?

The introduction of type-signatures require programmers to be more explicit in how functions behave.
This allows us to pin down more precisely where errors occur.

For example, in the `brownGetAcne` example, we could argue that the error is creating a column with the wrong name, or reading a column with the wrong name.
In the type-signature of `brownAndGetAcneTable`, we can specify whether the new column should be called `"part2"`, or `"brown and get acne"`.
In the former case, the error is when we try to use a column that doesn't exist in the `count`.
In the latter case, the error is when we try to use `buildColumn` to construct a column with the wrong name.

Similarly, in the `employeeToDepartment` example, we can specify whether `lastNameToDeptId` takes an employee table, or a department table.
In the former case, the error is when we attempt to call it with a department table.
In the latter case, the error is when we try to access the `"Last Name"` field of a department table.

> Q. Which error situations are prevented from being constructed? How?

All B2T2 example Error buggy programs are rejected by the Idris 2 type-checker.

All B2T2 example Error corrected programs compile successfully.

> Q. For each error situation that is at least partially expressible, what is the quality of feedback to the programmer?

The error messages may be unclear to programmers unfamiliar with dependently typed programming.

The issues with the Malformed Tables examples are mostly elaboration errors.
As `Table` literals are written using `SnocList` notation, Idris 2 attempts to find a usage of that notation that works.
As the example is incorrect, the `Table` `SnocList` notation doesn't work.
Naturally, the other `SnocList` notations also don't work, as we want a `Table`.

As Idris 2 does not distinguish "near miss" errors, it reports *all* `SnocList` notations in scope, saying what went wrong when it tried each of them.
This can be overwhelming for programmers unfamiliar with these sorts of error messages.

The issues with the Using Tables examples are mostly proof-search errors.
In particular, most of them are failures to find `Field` objects.

To call table operations that use a particular field, you need to prove that field is in the table.
You do this by providing a `Field schema name type` object, which is an index for a field called `name` of type `type` in schema `schema`.
If the schema is known at compile-time, then Idris 2 can generate these objects automatically.

At least, it can when the field exists in the schema.
If the field does not exist in the schema, the proof-search will fail, and Idris 2 will report that it "`Can't find an implementation for Field ...`".
This can be confusing for programmers unfamiliar with proof-search, as they may not find it obvious how some sort of "implementation" is related to asking for a field that doesn't exist.

Once they are familiar with this, however, the error message is useful, as it goes on to report the schema it was using, the name it was looking for, and the type it was expecting.

> Q. For each error situation that is prevented from being constructed, what is the quality of feedback to the programmer?

See previous question.
