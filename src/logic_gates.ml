type 'a z = [ `_0 of 'a] * 'a
type 'a o = [ `_1 of 'a] * 'a 

type ('a,'b,'c_in, 'r, 'c_out) adder = Adder
  (** Constraint on the inputs *)
  constraint
    'a = 'ma * 'fa
  constraint
    'ma = [< `_0 of 'fa | `_1 of 'fa ]
  constraint
    'b = 'mb * 'fb
  constraint
    'mb = [< `_0 of 'fb | `_1 of 'fb ]
  constraint
    'c_in = 'mcin * 'fcin
  constraint
    'mcin = [< `_0 of 'fcin | `_1 of 'fcin ]
  (** Logic table of the adder gate *)
  constraint
    'table =
    [< `_0 of
         [< `_0 of
              [< `_0 of [`_0 of 'r2 ] * [`_0 of 'c2] 
              | `_1 of [`_1 of 'r2 ] *  [`_0 of 'c2] ]
         | `_1 of
              [< `_0 of [`_1 of 'r2 ] *  [`_0 of 'c2]
              | `_1 of [`_0 of 'r2 ] *  [`_1 of 'c2] ]
         ]
    | `_1 of
         [< `_0 of
              [< `_0 of [ `_1 of 'r2 ] * [`_0 of 'c2]
              | `_1 of [ `_0 of 'r2 ] * [`_1 of 'c2] ]
         | `_1 of
              [< `_0 of [ `_0 of 'r2 ] * [`_1 of 'c2]
              | `_1 of [ `_1 of 'r2 ] * [`_1 of 'c2] ]
         ]
    ]
  (** Assembling the argument *)
   constraint
     'fa = 'mb
   constraint
     'fb = 'mcin
   (** Unify the assembled argument with the result table  *)     
   constraint
     'table = 'ma
   (** Grab the results exposed in 'fcin *)
   constraint
     'fcin = 'er * 'ec
   (** Create the output *)
   constraint
     'r = 'er * 'r2
   constraint
     'c_out = 'ec * 'c2

type ('mult, 'b, 's) mult = Mult
  constraint
    'mult = 'mp * 'fm
  constraint
    'mp = [< `_1 of 'fm | `_0 of 'fm ]
  constraint
    'b = 'bp * 'fb
  constraint
    'bp = [< `_1 of 'fb | `_0 of 'fb ]
  constraint
    'table = [< `_1 of
                  [< `_1 of [`_1 of 'ss]
                  |  `_0 of [`_0 of 'ss]  ]
             | `_0 of
                  [< `_1 of [`_0 of 'ss]
                  |  `_0 of [`_0 of 'ss]  ]
             ]
  constraint
    'fm = 'bp
  constraint
    'mp = 'table
  constraint
    's = 'fb * 'ss

type ('a,'clone1,'clone2) cloner = Cloner
  constraint
    'a = 'ma * 'fa
  constraint
    'ma = [< `_0 of 'fa | `_1 of 'fa]
  constraint
    'table = [< `_0 of
                  ( [`_0 of 'fcl1] * 'fcl1 )
                  * ( [`_0 of 'fcl2] * 'fcl2 )
             | `_1 of
                  ( [`_1 of 'fcl1] * 'fcl1 )
                  * ( [`_1 of 'fcl2] * 'fcl2 )
             ]
  constraint
    'ma = 'table
  constraint
    'clone1 * 'clone2 = 'fa

type ('a, 'clone1, 'clone2, 'clone3) cloner2 = Cloner2
  constraint
    'a = 'ma * 'fa
  constraint
    'ma = [< `_0 of 'fa | `_1 of 'fa]
  constraint
    'table = [<
    |`_0 of ([ `_0 of 'f1] * 'f1) *([ `_0 of 'f2] * 'f2) * ([ `_0 of 'f3] * 'f3)
    | `_1 of ([ `_1 of 'f1] * 'f1) *([ `_1 of 'f2] * 'f2) * ([ `_1 of 'f3] * 'f3)
  ]
  constraint
    'ma = 'table
  constraint
    'clone1 * 'clone2 * 'clone3 = 'fa


type ('a,'b,'gor) g_or = Or
  constraint
    'a = 'ma * 'fa
  constraint
    'ma = [< `_0 of 'fa | `_1 of 'fa]
  constraint
    'b = 'mb * 'fb
  constraint
    'mb = [< `_0 of 'fb | `_1 of 'fb]
  constraint
    'table =
    [<
      | `_0 of
        [<
          |`_0 of [ `_0 of 'flor]
          | `_1 of [ `_1 of 'flor]
        ]
      | `_1 of
        [<
          |`_0 of [ `_1 of 'flor]
          | `_1 of [ `_1 of 'flor]
        ]
    ]
  constraint
  'fa = 'mb
  constraint
    'ma = 'table
  constraint
    'gor = 'fb * 'flor

type ('s1,'s2, 'c, 's, 'overflow) overflow = Overflow
  constraint
    's1 = 'ms1 * 'f1
  constraint
    'ms1 = [< `_0 of 'f1 | `_1 of 'f1]
  constraint
    's2 = 'ms2 * 'f2
  constraint
    'ms2 = [< `_0 of 'f2 | `_1 of 'f2]
  constraint
    'c = 'mc * 'fc
  constraint
    'mc = [< `_0 of 'fc | `_1 of 'fc]
  constraint
    'table =
    [<
      | `_0 of
          [<
            |`_0 of [<
                | `_0 of [ `_0 of 'fs] * [`_0 of 'fo]
                | `_1 of [ `_1 of 'fs] * [`_1 of 'fo]
              ]
            | `_1 of ( [<
                  | `_0 of [ `_1 of 'fs] * [`_0 of 'fo]
                  | `_1 of [ `_0 of 'fs] * [`_0 of 'fo]
                ] as 'no_overflow )
          ]
      | `_1 of
          [<
            |`_0 of 'no_overflow
            | `_1 of [<
                | `_0 of [ `_1 of 'fs] * [`_0 of 'fo]
                | `_1 of [ `_0 of 'fs] * [`_1 of 'fo]
              ]
          ]
    ]
  constraint
  'f1 = 'ms2
  constraint
    'f2 = 'mc
  constraint
    'ms1 = 'table
  constraint
    'fc = 'ms * 'mo
  constraint
    's = 'ms * 'fs
  constraint
    'overflow = 'mo * 'fo

type ('a,'flip) flip = Flip
  constraint
    'a = 'ma * 'fa
  constraint
    'ma = [< `_0 of 'fa | `_1 of 'fa]
  constraint
    'table =
    [<
      | `_0 of [ `_1 of 'f]
      | `_1 of [ `_0 of 'f]
    ]
  constraint
    'ma = 'table
  constraint
    'flip = 'fa * 'f


type ('control,'a,'b, 'eq ) eq_chain = Eqc
  (** Constraint on the inputs *)
  constraint
    'a = 'ma * 'fa
  constraint
    'ma = [< `_0 of 'fa | `_1 of 'fa ]
  constraint
    'b = 'mb * 'fb
  constraint
    'mb = [< `_0 of 'fb | `_1 of 'fb ]
  constraint
    'control = 'mc * 'fc
  constraint
    'mc = [< `_0 of 'fc | `_1 of 'fc ]
  (** Logic table of the adder gate *)
  constraint
    'table =
    [< `_0 of
         [< `_0 of (
              [< `_0 of ( [`_0 of 'feq ] as 'z) 
              | `_1 of 'z ] as 'z2)
         | `_1 of 'z2 ]
    | `_1 of
         [< `_0 of
              [< `_0 of ([ `_1 of 'feq ] as 'o) 
              | `_1 of 'z ]
         | `_1 of
              [< `_0 of 'z
              | `_1 of 'o ]
         ]
    ]
  (** Assembling the argument *)
   constraint
     'fc = 'ma
   constraint
     'fa = 'mb
   (** Unify the assembled argument with the result table  *)     
   constraint
     'table = 'mc
   (** Create the output *)
   constraint
     'eq = 'fb * 'feq
