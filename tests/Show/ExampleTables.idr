import Data.Table

exampleTable : Table [<
    "name" :! String,
    "age" :! Nat,
    "quizzes" :! Table [<"quiz#" :! Nat, "grade" :! Nat],
    "midterm" :! Nat,
    "final" :! Nat
  ]
exampleTable = [<
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

exampleFrame : Frame [<
    "name" :! String,
    "age" :! Nat,
    "quizzes" :! Table [<"quiz#" :! Nat, "grade" :! Nat],
    "midterm" :! Nat,
    "final" :! Nat
  ] 3
exampleFrame = [<
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
