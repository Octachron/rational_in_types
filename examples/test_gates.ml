module N = Natural
module L = Logic_gates
open L

let one: 'a o N.t = N.create 1
let zero: 'a z N.t = N.create 0    

let one': 'a o N.t = N.create 1
let zero': 'a z N.t = N.create 0    

let one'': 'a o N.t = N.create 1
let zero'': 'a z N.t = N.create 0    


let or_ : ('a,'b,'c) or_ -> 'a N.t -> 'b N.t -> 'c N.t =
  fun _ x y ->N.( create @@ to_int x lor to_int y )

let t =
  or_ L.Or one zero
    
let eq: ('c,'x,'y,'eq) eq_chain -> 'c N.t -> 'x N.t -> 'y N.t -> 'eq N.t =
  fun _ c x y ->
    N.( create @@ if (to_int c =0) && to_int x= to_int y then 1 else 0 )

let eq x y= eq L.Eqc x y
    
let eq_test =
  eq one one' one''

let add : ('a,'b, _ z, 'c0, 'c1) adder -> 'a N.t -> 'b N.t -> <b0:'c0; b1:'c1> N.t  = fun _ x y -> N.( create @@ to_int x + to_int y )

let test = add Adder one' one

let clone: ('a,'b,'c) cloner -> 'a N.t -> 'b N.t * 'c N.t =
  fun _ x -> N.( transmute x, transmute x )

let (o1,o2) = clone Cloner zero


let clone2: ('a,'b,'c,'d) cloner2 -> 'a N.t -> 'b N.t * 'c N.t * 'd N.t =
  fun _ x -> N.( transmute x, transmute x, transmute x )

let (o1,o2,o3) = clone2 Cloner2 zero

let if_ :('a,'b,'c,'r) if_ -> 'a N.t -> 'b N.t -> 'c N.t -> 'r N.t =
  fun _ a b c ->
    let open N in
    if to_int a = 0 then transmute b else transmute c

type exotic = Exotic
let if_ a b = if_ If a b
let z = if_ zero (N.create 0: exotic N.t) one'
let o = if_ one zero one'
