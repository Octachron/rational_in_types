“ And with strange aeons, even types may multiply ”

This library is essentially a brain teaser, where types are twisted
and tortured for the sake of type-level arithmetic. Neither usability
nor sanity should be expected here.


Using and abusing polymorphic variants, this library implements all ring
operations over rational with fixed precision numerator and denominator at
the type level. Only 3 bits fixed-precision integers are implemented, it is
not clear how much further the OCaml compiler can be tortured by adding
more bits.


The integer representation used is quite simple:
The bit `0` and `1` are represented by
```OCaml
type 'a z = [ `_0 of 'a ]
type 'a o = [ `_1 of 'a ]
```
An integer `n` with three bits `n_0,n_1,n_2` is mapped to the object type
```
<b0: _ n_0; b_1: _ n_1; b_2: _ n_2; overflow: _ z>
```
It is then possible to use polymorphic variant to implement any boolean
functions. A potential useful intermediary for humans is to implements
logical gates.

For instance, flipping a bit `'a` can be accomplished by the function

```OCaml
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
```
Note that the type of `'a` is consumed by the function flip and the result is
stored inside the type `'flip`. This implies that integer types can be used only
once in any type level computation. Fortunately, it is also possible to implements
a cloning function as

```OCaml
type ('a,'clone1,'clone2) cloner = Cloner
  constraint
    'a = [< `_0 of ( ('clone1 * 'clone2) as 't)  | `_1 of 't]
  constraint
    'table = [< `_0 of 'b z * ' c z
             | `_1 of 'b o * 'c o
             ]
  constraint
    'a = 'table
```

An adder gate goes one step further with three input and two outputs
```OCaml
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

```
