module B2T2.ExampleTables

import public Data.Table
import public Data.Vect

%default total

public export
students : Table [<"name" :! String, "age" :! Nat, "favorite color" :! String]
students = [<
    [<"Bob",   12, "blue" ],
    [<"Alice", 17, "green"],
    [<"Eve",   13, "red"  ]
  ]

public export
studentsMissing : Table [<"name" :! String, "age" :! Maybe Nat, "favorite color" :! Maybe String]
studentsMissing = [<
    [<"Bob",   Nothing, Just "blue" ],
    [<"Alice", Just 17, Just "green"],
    [<"Eve",   Just 13, Nothing     ]
  ]

public export
employees : Table [<"Last Name" :! String, "Department ID" :! Maybe Nat]
employees = [<
    [<"Rafferty",   Just 31],
    [<"Jones",      Just 32],
    [<"Heisenberg", Just 33],
    [<"Robinson",   Just 34],
    [<"Smith",      Just 34],
    [<"Williams",   Nothing]
  ]

public export
departments : Table [<"Department ID" :! Nat, "Department Name" :! String]
departments = [<
    [<31, "Sales"      ],
    [<33, "Engineering"],
    [<34, "Clerical"   ],
    [<35, "Marketing"  ]
  ]

public export
jellyAnon : Table [<
    "get acne" :! Bool,
    "red" :! Bool,
    "black" :! Bool,
    "white" :! Bool,
    "green" :! Bool,
    "yellow" :! Bool,
    "brown" :! Bool,
    "orange" :! Bool,
    "pink" :! Bool,
    "purple" :! Bool
  ]
jellyAnon = [<
    [<True,  False, False, False, True,  False, False, True,  False, False],
    [<True,  False, True,  False, True,  True,  False, False, False, False],
    [<False, False, False, False, True,  False, False, False, True,  False],
    [<False, False, False, False, False, True,  False, False, False, False],
    [<False, False, False, False, False, True,  False, False, True,  False],
    [<True,  False, True,  False, False, False, False, True,  True,  False],
    [<False, False, True,  False, False, False, False, False, True,  False],
    [<True,  False, False, False, False, False, True,  True,  False, False],
    [<True,  False, False, False, False, False, False, True,  False, False],
    [<False, True,  False, False, False, True,  True,  False, True,  False]
  ]

public export
jellyNamed : Table [<
    "name" :! String,
    "get acne" :! Bool,
    "red" :! Bool,
    "black" :! Bool,
    "white" :! Bool,
    "green" :! Bool,
    "yellow" :! Bool,
    "brown" :! Bool,
    "orange" :! Bool,
    "pink" :! Bool,
    "purple" :! Bool
  ]
jellyNamed = [<
    [<"Emily",    True,  False, False, False, True,  False, False, True,  False, False],
    [<"Jacob",    True,  False, True,  False, True,  True,  False, False, False, False],
    [<"Emma",     False, False, False, False, True,  False, False, False, True,  False],
    [<"Aidan",    False, False, False, False, False, True,  False, False, False, False],
    [<"Madison",  False, False, False, False, False, True,  False, False, True,  False],
    [<"Ethan",    True,  False, True,  False, False, False, False, True,  True,  False],
    [<"Hannah",   False, False, True,  False, False, False, False, False, True,  False],
    [<"Matthew",  True,  False, False, False, False, False, True,  True,  False, False],
    [<"Hailey",   True,  False, False, False, False, False, False, True,  False, False],
    [<"Nicholas", False, True,  False, False, False, True,  True,  False, True,  False]
  ]

public export
gradebook : Table [<
    "name" :! String,
    "age" :! Nat,
    "quiz1" :! Nat,
    "quiz2" :! Nat,
    "midterm" :! Nat,
    "quiz3" :! Nat,
    "quiz4" :! Nat,
    "final" :! Nat
  ]
gradebook = [<
    [<"Bob",   12, 8, 9, 77, 7, 9, 87],
    [<"Alice", 17, 6, 8, 88, 8, 7, 85],
    [<"Eve",   13, 7, 9, 84, 8, 8, 77]
  ]

public export
gradebookMissing : Table [<
    "name" :! String,
    "age" :! Nat,
    "quiz1" :! Maybe Nat,
    "quiz2" :! Maybe Nat,
    "midterm" :! Maybe Nat,
    "quiz3" :! Maybe Nat,
    "quiz4" :! Maybe Nat,
    "final" :! Maybe Nat
  ]
gradebookMissing = [<
    [<"Bob",   12, Just 8,  Just 9, Just 77, Just 7,  Just 9, Just 87],
    [<"Alice", 17, Just 6,  Just 8, Just 88, Nothing, Just 7, Just 85],
    [<"Eve",   13, Nothing, Just 9, Just 84, Just 8,  Just 8, Just 77]
  ]

public export
gradebookSeq : Table [<
    "name" :! String,
    "age" :! Nat,
    "quizzes" :! Vect 4 Nat,
    "midterm" :! Nat,
    "final" :! Nat
  ]
gradebookSeq = [<
    [<"Bob",   12, [8, 9, 7, 9], 77, 87],
    [<"Alice", 17, [6, 8, 8, 7], 88, 85],
    [<"Eve",   13, [7, 9, 8, 8], 84, 77]
  ]

public export
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
