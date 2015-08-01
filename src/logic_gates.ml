module N = Natural
open N

type 'a z = [ `_0 of 'a]
type 'a o = [ `_1 of 'a]

type ('a,'b,'c, 'r, 'c_out) adder = Adder
  (** Constraint on the inputs *)
  constraint
    'a = [< `_0 of 'b | `_1 of 'b ]
  constraint
    'b = [< `_0 of 'c | `_1 of 'c ]
  constraint
    'c = [< `_0 of ( 'r*'c_out as 't) | `_1 of 't ] 
  (** Logic table of the adder gate *)
  constraint
    'table =
    [< `_0 of
         [< `_0 of
              [< `_0 of ('r2 z as 'r2_0) * ( 'c2 z as 'c2_0) 
              | `_1 of ( 'r2 o as 'r2_1) *  'c2_0 ]
         | `_1 of
              [< `_0 of 'r2_1 *  'c2_0
              | `_1 of 'r2_0 *  ('c2 o as 'c2_1) ]
         ]
    | `_1 of
         [< `_0 of
              [< `_0 of 'r2_1 * 'c2_0
              | `_1 of 'r2_0 * 'c2_1 ]
         | `_1 of
              [< `_0 of 'r2_0 * 'c2_1
              | `_1 of 'r2_1 * 'c2_1 ]
         ]
    ]
   constraint
     'table = 'a


type ('mult, 'b, 's) mult = Mult
  constraint
    'mult = [< `_1 of 'b | `_0 of 'b ]
  constraint
    'b = [< `_1 of 's | `_0 of 's ]
  constraint
    'table = [< `_1 of
                  [< `_1 of 'ss o
                  |  `_0 of ('ss z as 'o)  ]
             | `_0 of
                  [< `_1 of 'o
                  |  `_0 of 'o]
             ]
  constraint
    'mult = 'table

type ('a,'clone1,'clone2) cloner = Cloner
  constraint
    'a = [< `_0 of ( ('clone1 * 'clone2) as 't)  | `_1 of 't]
  constraint
    'table = [< `_0 of 'b z * ' c z 
             | `_1 of 'b o * 'c o
             ]
  constraint
    'a = 'table

type ('a, 'clone1, 'clone2, 'clone3) cloner2 = Cloner2
  constraint
    'a = [< `_0 of ( ('clone1 * 'clone2 * 'clone3 ) as 't)  | `_1 of 't]
  constraint
    'ma = [< `_0 of 'fa | `_1 of 'fa]
  constraint
    'table = [<
    |`_0 of 'b z * 'c z * 'd z
    | `_1 of 'b o * 'c o * 'd o
  ]
  constraint
    'a = 'table

type ('a,'b,'or_) or_ = Or
  constraint
    'a = [< `_0 of 'b | `_1 of 'b]
  constraint
    'b = [< `_0 of 'or_ | `_1 of 'or_]
  constraint
    'table =
    [<
      | `_0 of
        [<
          |`_0 of 'c z
          | `_1 of 'c o
        ]
      | `_1 of
        [<
          |`_0 of 'c o
          | `_1 of 'c o
        ]
    ]
  constraint
  'a = 'table

type ('a,'b, 'c, 's, 'overflow) overflow = Overflow
  constraint
    'a = [< `_0 of 'b | `_1 of 'b]
  constraint
    'b = [< `_0 of 'c | `_1 of 'c]
  constraint
    'c = [< `_0 of ('s * 'overflow as 't) | `_1 of 't]
  constraint
    'table =
    [<
      | `_0 of
          [<
            |`_0 of [<
                | `_0 of ('ts z * 'ov z as 'zz)
                | `_1 of 'ts o * 'ov o
              ]
            | `_1 of ( [<
                  | `_0 of ('ts o * 'ov z as 'oz)
                  | `_1 of 'zz
                ] as 'no_overflow )
          ]
      | `_1 of
          [<
            |`_0 of 'no_overflow
            | `_1 of [<
                | `_0 of 'oz
                | `_1 of 'ts z * 'ov o
              ]
          ]
    ]
  constraint
    'a = 'table


type ('a,'flip) flip = Flip
  constraint
    'a = [< `_0 of 'flip | `_1 of 'flip]
  constraint
    'table =
    [<
      | `_0 of [ `_1 of 'f]
      | `_1 of [ `_0 of 'f]
    ]
  constraint
    'a = 'table

type ('control,'a,'b, 'eq ) eq_chain = Eqc
  (** Constraint on the inputs *)
  constraint
    'control = [< `_0 of 'a | `_1 of 'a ]
  constraint
    'a = [< `_0 of 'b | `_1 of 'b ]
  constraint
    'b = [< `_0 of 'eq | `_1 of 'eq ]
   (** Logic table *)
  constraint
    'table =
    [< `_0 of
         [< `_0 of (
              [< `_0 of ( 'feq z  as 'z)
              | `_1 of 'z ] as 'z2)
         | `_1 of 'z2 ]
    | `_1 of
         [< `_0 of
              [< `_0 of ( 'feq o as 'o) 
              | `_1 of 'z ]
         | `_1 of
              [< `_0 of 'z
              | `_1 of 'o ]
         ]
    ]
  (** Assembling the argument *)
   constraint
     'control = 'table
