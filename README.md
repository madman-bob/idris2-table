# Idris2-Table

A table library for Idris 2.

## Install

Run:

```bash
make install
```

## Usage

Build your code with the `table` package, and import the `Data.Table` module.

### Example

Examples here and in the tests are taken from [B2T2](https://blog.brownplt.org/2021/11/21/b2t2.html) benchmark examples.

Tables are of type `Table schema`, where a `Schema` is a description of the columns of the table.

```idris
import Data.Table

gradebook : Table [<"name" :! String, "age" :! Nat, "midterm" :! Nat, "final" :! Nat]
gradebook = [<
    [<"Bob",   12, 77, 87],
    [<"Alice", 17, 88, 85],
    [<"Eve",   13, 84, 77]
  ]

```

Accessing a field requires a proof that field exists in the schema.
We can prove that a schema has a certain field by constructing a proof object of type `HasField schema name type`.

For simple examples, Idris can find these proofs automatically:

```idris-repl
Main> column "name" gradebook
[<"Bob", "Alice", "Eve"]
```

For a more complicated example, you may need to construct them yourself:

```idris
grades : Bool -> SnocList Nat
grades getFinal = do
    let (fld ** prf) = the (fld : String ** HasField _ fld Nat) $ if getFinal
        then ("final" ** %search)
        else ("midterm" ** %search)
    column fld @{prf} gradebook
```
