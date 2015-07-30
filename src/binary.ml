open Natural
open Logic_gates
    
type 'a zero = [ `_0 of 'a ] * 'a
type 'a one = [`_1 of 'a ] * 'a

let _0 : 'a zero  t = create 0
let _1 : 'one t = create 1
    

module Exploration = struct

let p_1:
  ( [< `_0 of [< `_0 of [`_0 of [`_1 of 'a ] ] | `_1 of [`_1 of [`_0 of 'a] ]  ]
  | `_1 of [< `_0 of [`_1 of [`_1 of 'a ] ] | `_1 of [`_0 of [`_0 of 'a ] ]  ]
  ] * 'a ) t = create 1
  
let _00 : ([ `_0 of [ `_0 of 'a] ] * 'a) t = create 0

let _01 : ([ `_0 of [`_1 of 'b ] ] * 'b) t = create 1
let _10 : ([ `_1 of [ `_0 of 'a] ] * 'a) t = create 2
let _11 : ([ `_1 of [`_1 of 'b ] ] * 'b) t = create 3

let add: ('a*'b) t -> ('a * 'c) t -> ('b * 'c) t  = fun num adder ->
  create @@ to_int p_1 + to_int num 

let n  =
  add _01 p_1
end

let add : ('a,'b, [`_0 of 'c] * 'c ,'r,'c_out) adder -> 'a t -> 'b t -> 'r t * 'c_out t = fun adder k l ->
  create @@ ( to_int k + to_int l) mod 2,
  create @@ (to_int k land to_int l)

let (n, r) =
  add Adder _1 _1
    
type nil
type _ list =
  | Nil : < list: nil > list
  | Cons: 'a * < list: 'l > list -> < list: 'a -> 'l > list
      
     
let add2 :
  < list :
      ('a1,'b1, [`_0 of 'c0] * 'c0 ,'r1,'c1) adder
      -> ('a2,'b2, 'c1 ,'r2,'c_out) adder
      -> nil   
  > list
  -> < list: 'a1 t -> 'a2 t -> nil > list
  -> < list: 'b1 t -> 'b2 t -> nil > list
  -> < list: 'r1 t -> 'r2 t -> nil > list =
  fun%with_ll adders [a1; a2] [ b1; b2 ] ->
  [ create @@ ( to_int a1 + to_int b1) mod 2 ; create @@ (to_int a2 + to_int b2 ) mod 2 ] 

let _ =
  let%with_ll [b1;b2] = 
    add2 [Adder; Adder] [_0; _1 ][_1; _0] in
  to_int b1


let sum a0 b0  a1 b1 = create @@ (to_int a1 + to_int b1 + (to_int a0 land to_int b0) ) mod 2 

let add8 :
  < list :
      ('a1,'b1, [`_0 of 'c0] * 'c0 ,'r1,'c1) adder
      -> ('a2,'b2, 'c1 ,'r2,'c2) adder
      -> ('a3,'b3, 'c2 ,'r3,'c3) adder
      -> ('a4,'b4, 'c3 ,'r4,'c4) adder
      -> ('a5,'b5, 'c4 ,'r5,'c5) adder
      -> ('a6,'b6, 'c5 ,'r6,'c6) adder
      -> ('a7,'b7, 'c6 ,'r7,'c7) adder
      -> ('a8,'b8, 'c7 ,'r8,'c8) adder
      -> nil   
  > list
  -> < list:
         ( 'a1 * ('a2 * ('a3 * ('a4 * ('a5 * ('a6 * ('a7 * ('a8 * nil))))))))
     > t
  -> < list:
         ( 'b1 * ('b2 * ('b3 * ('b4 * ('b5 * ('b6 * ('b7 * ('b8 * nil))))))))
     > t
  -> < list:
         ( 'r1 * ('r2 * ('r3 * ('r4 * ('r5 * ('r6 * ('r7 * ('r8 * nil))))))))
     > t =
  fun adders a b -> create ( to_int a + to_int b mod 8)

let%with_ll g8 = [
  Adder; Adder; Adder; Adder; Adder; Adder; Adder; Adder
]

let _0b : <list: ([`_0 of 'a] * 'a) * nil > t = create 0
let _1b : < list : ([`_1 of 'a] * 'a) * nil > t = create 1
    
let _0 : < list: 'l> t ->  < list: ([`_0 of 'a] * 'a) * 'l > t
  = fun nat -> create @@ 2 * to_int nat
      
let _1 : < list: 'l> t ->  < list: ([`_1 of 'a] * 'a) * 'l > t
  = fun nat -> create @@ 1 + 2 * to_int nat

let a = _0 @@ _1 @@ _1 @@ _0 @@ _1 @@ _1 @@ _0 @@ _0b 
let b = _0 @@ _0 @@ _0 @@ _0 @@ _0 @@ _1 @@ _0 @@ _1b


let three = _1 @@ _1b
let two = _0 @@ _1b



let n =
  let r = 
    add8 g8 a b in
  to_int r


let lsl1: <list: 'l > t -> < list: 'a zero -> 'l > t = fun n ->
  create @@ (to_int n) lsl 1

let lsl2: <list: 'l > t -> < list: 'a zero -> 'b zero -> 'l > t = fun n ->
  create @@ (to_int n) lsl 1


  


                 

let copy : ('digit, 'cl1,'cl2) cloner -> 'digit t -> 'cl1 t * 'cl2 t =
  fun _ nat ->
    let n = to_int nat in
    polycreate.f n, polycreate.f n                


let (c1, c2) = copy Cloner @@ ( create 1 : ( [`_0 of 'a ] * 'a ) t )  
    

let mult1 : ('digit,'b,'s) mult -> 'digit t -> 'b t -> 's t =
  fun gate m x -> create @@ to_int m * to_int x 

let m =
  let m : ([`_0 of 'a] * 'a) t = create 1 in
  let x : ([`_1 of 'b] * 'b) t = create 1 in
  let r = mult1 Mult m x in
  r


let%with_ll g2 = [Adder; Adder]

let mult2:
  ('m1,'m1a,'m1b) cloner * ('b1,'b1a,'b1b) cloner 
  * ('m1a,'b1a,'r1) mult * ('m1b,'b2,'s2) mult
  * ('m2,'b1b,'s2b) mult
  * ('s2, 's2b, [`_0 of 'k ] * 'k, 'r2, 'cout) adder
  -> <list: 'b1 * ('b2 * nil) > t -> <list: 'm1 * ('m2 * nil) > t
  -> <list: 'r1 * ('r2 * nil) > t =
  fun _ x y -> create @@ ( to_int x * to_int y mod 4)  


let two = mult2 (Cloner,Cloner,Mult,Mult,Mult,Adder) three two


let add1 n =
  add8 g8 ( _1 @@ _0 @@ _0 @@ _0 @@ _0 @@ _0 @@ _0 @@ _0b  ) n

let k = add1 a

 (* 
type _ adder=
    Nil : <
      a: nil;
      b:nil;
      r:nil;
      ci: ([`_0 of 'c0] * 'c0) -> nil ;
      co: nil
    > adder
  | Cons:
      ('a,'b, 'c_in, 'r,'c_out) adder_gate
      * <
      a: 'a_s;
      b: 'b_s;
      r: 'r_s;
      ci: 'ci;
      co: 'co 
      > adder
    -> <
      a: 'a -> 'a_s;
      b: 'b -> 'b_s;
      r: 'r -> 'r_s;
      ci: 'c_in -> 'ci;
      co: 'c_out -> 'co;
    > adder
*)

