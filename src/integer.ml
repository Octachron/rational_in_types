module N = Natural
module L = Logic_gates
open L
type +'a t = 'a N.t
  constraint
    'a = < b0:'b0; b1:'b1; b2:'b2; s:'s; overflow:'o >

type tautology = True
let assert_no_overflow : <overflow: 'any z; .. > t -> 'a t = fun n -> n 

let z : < b0:'b0 z; b1:'b1 z; b2:'b2 z; s:'s z; overflow:'o z > t  = N.create 0
let one : < b0:'b0 o; b1:'b1 z; b2:'b2 z; s:'s z; overflow:'o z > t  = N.create 1
let m_one : < b0:'b0 o; b1:'b1 o; b2:'b2 o; s:'s o; overflow:'o z > t  = N.create ~-1

let duplicate:
  ('o0,'o1,'o2) cloner * ('b0_0,'b0_1,'b0_2) cloner
  * ('b1_0,'b1_1,'b1_2) cloner * ('b2_0,'b2_1,'b2_2) cloner
  * ('s0,'s1,'s2) cloner
  -> < b0:'b0_0; b1: 'b1_0; b2: 'b2_0; s:'s0; overflow:'o0> t
  -> < b0:'b0_1; b1: 'b1_1; b2: 'b2_1; s:'s1; overflow:'o1> t
  *  < b0:'b0_2; b1: 'b1_2; b2: 'b2_2; s:'s2; overflow:'o2> t =
  fun _ x -> N.(polytransmute.t x, polytransmute.t x)                              

let duplicate x =
  duplicate L.(Cloner,Cloner,Cloner,Cloner,Cloner) x

let duplicate2:
  ('o0,'o1,'o2, 'o3) cloner2 * ('a0,'b0,'c0,'d0) cloner2
  * ('a1,'b1,'c1,'d1) cloner2 * ('a2,'b2,'c2,'d2) cloner2
  * ('s0,'s1,'s2,'s3) cloner2
  -> < b0:'a0; b1: 'a1; b2: 'a2; s:'s0; overflow:'o0> t
  -> < b0:'b0; b1: 'b1; b2: 'b2; s:'s1; overflow:'o1> t
  *  < b0:'c0; b1: 'c1; b2: 'c2; s:'s2; overflow:'o2> t
  *  < b0:'d0; b1: 'd1; b2: 'd2; s:'s3; overflow:'o3> t =
  fun _ x -> N.(polytransmute.t x, polytransmute.t x, polytransmute.t x)    

let duplicate2 x = duplicate2 (Cloner2,Cloner2,Cloner2,Cloner2,Cloner2) x

let add:
  ('b0_0,'b0_1,'fresh z,'b0_2,'c1) adder 
 * ('b1_0,'b1_1,'c1,'b1_2,'c2) adder
 * ('b2_0,'b2_1,'c2,'b2_2,'c3) adder
 * ('s0,'s1,'c3,'s2,'overflow) overflow
 * ('o0,'o1,'o01) or_
 * ('o01,'overflow,'o2) or_
  -> < b0:'b0_0; b1: 'b1_0; b2: 'b2_0; s: 's0; overflow:'o0> t
  -> < b0:'b0_1; b1: 'b1_1; b2: 'b2_1; s: 's1; overflow:'o1> t
  -> < b0:'b0_2; b1: 'b1_2; b2: 'b2_2; s: 's2; overflow:'o2> t =
  fun _ x y -> N.( create @@ to_int x + to_int y)                             

let add x y =
  add (Adder,Adder,Adder,Overflow,Or,Or) x y

let flip:
  ('a0,'b0) flip * ('a1,'b1) flip * ('a2,'b2) flip * ('s1,'s2) flip
  -> < b0:'a0; b1: 'a1; b2: 'a2; s: 's1; overflow:'o1> t   
  -> < b0:'b0; b1: 'b1; b2: 'b2; s: 's2; overflow:'o1> t =
  fun _ n -> N.create @@ -N.to_int n - 1 

let flip n = flip (Flip,Flip,Flip,Flip) n

let uminus n =
  add one @@ flip n

let m_one' = uminus one

let minus a b = add a @@ uminus b  

let lsl_1 :
  ('o,'b2,'o2) L.or_ ->
  < b0:'b0; b1:'b1; b2:'b2; s:'s; overflow:'o > t ->
  < b0:'fresh z; b1:'b0; b2:'b1; s:'s; overflow:'o2 > t =
  fun _ x -> N.create @@ N.to_int x lsl 1  

let lsl_1 x  = lsl_1 Or x
    
let mult :
  ('a0,'a0_r, 'a0_r2,'a0_0) cloner2 * ('a0_r,'a0_1, 'a0_2, 'a0_3) cloner2
  * ('a0_r2,'a0_4,'a0_5,'a0_6) cloner2

  * ('a1,'a1_r, 'a1_r2,'a1_0) cloner2 * ('a1_r,'a1_1, 'a1_2, 'a1_3) cloner2
  * ('a1_r2,'a1_4,'a1_5) cloner

  * ('a2,'a2_r, 'a2_0,'a2_1) cloner2 * ('a2_r,'a2_2, 'a2_3, 'a2_4) cloner2

  * ('sa,'a3_r, 'a4, 'a3_0) cloner2 * ('a3_r,'a3_1, 'a3_2, 'a3_3) cloner2

 * ('a4,'a4_r, 'a5, 'a4_0) cloner2 * ('a4_r,'a4_1, 'a4_2) cloner

 * ('a5,'a6_0, 'a5_0, 'a5_1) cloner2


  * ('b0,'b0_r, 'b0_r2,'b0_0) cloner2 * ('b0_r,'b0_1, 'b0_2, 'b0_3) cloner2
  * ('b0_r2,'b0_4,'b0_5,'b0_6) cloner2

  * ('b1,'b1_r, 'b1_r2,'b1_0) cloner2 * ('b1_r,'b1_1, 'b1_2, 'b1_3) cloner2
  * ('b1_r2,'b1_4,'b1_5) cloner

  * ('b2,'b2_r, 'b2_0,'b2_1) cloner2 * ('b2_r,'b2_2, 'b2_3, 'b2_4) cloner2

  * ('sb,'b3_r, 'b4, 'b3_0) cloner2 * ('b3_r,'b3_1, 'b3_2, 'b3_3) cloner2

  * ('b4,'b4_r, 'b5, 'b4_0) cloner2 * ('b4_r,'b4_1, 'b4_2) cloner
    
  * ('b5,'b6_0, 'b5_0, 'b5_1) cloner2

  *('a0_0, 'b0_0, 'c0) mult * ('a0_1,'b1_0,'c1_0) mult * ('a0_2,'b2_0, 'c2_0 ) mult
  *('a0_3, 'b3_0, 'c3_0) mult * ('a0_4, 'b4_0, 'c4_0) mult
  * ('a0_5, 'b5_0, 'c5_0) mult * ('a0_6, 'b6_0, 'c6_0) mult
    
  *('a1_0, 'b0_1, 'c1_1) mult * ('a1_1,'b1_1,'c2_1) mult * ('a1_2,'b2_1, 'c3_1 ) mult
  *('a1_3, 'b3_1, 'c4_1) mult * ('a1_4, 'b4_1, 'c5_1) mult
  *('a1_5, 'b5_1, 'c6_1) mult

  *('a2_0, 'b0_2, 'c2_2) mult * ('a2_1,'b1_2,'c3_2) mult * ('a2_2,'b2_2, 'c4_2 ) mult
  *('a2_3, 'b3_2, 'c5_2) mult * ('a2_4, 'b4_2, 'c6_2) mult

  *('a3_0, 'b0_3, 'c3_3) mult * ('a3_1,'b1_3,'c4_3) mult * ('a3_2,'b2_3, 'c5_3 ) mult
  *('a3_3, 'b3_3, 'c6_3) mult

  *('a4_0, 'b0_4, 'c4_4) mult * ('a4_1,'b1_4,'c5_4) mult * ('a4_2,'b2_4, 'c6_4 ) mult

  *('a5_0, 'b0_5, 'c5_5) mult * ('a5_1,'b1_5,'c6_5) mult

  *('a6_0, 'b0_6, 'c6_6) mult

  * ('c1_0,'c1_1, _ z, 'c1, 'c2_3) adder

  * ('c2_0,'c2_1,'c2_2,'c2_4,'c3_4) adder * ('c2_3,'c2_4,_ z,'c2, 'c3_5) adder

  * ('c3_0,'c3_1,'c3_2,'c3_6,'c4_5) adder * ('c3_3,'c3_4,'c3_5,'c3_7, 'c4_6) adder
  * ('c3_6,'c3_7,_ z, 'c3_r, 'c4_7) adder
    
  *('c4_0,'c4_1,'c4_2,'c4_8,'c5_6) adder * ('c4_3,'c4_4,'c4_5,'c4_9, 'c5_7) adder
  *('c4_6,'c4_7, 'c4_8, 'c4_10, 'c5_8) adder * ('c4_9,'c4_10, _ z, 'c4, 'c5_9) adder 

  *('c5_0,'c5_1,'c5_2,'c5_10,'c6_7) adder * ('c5_3,'c5_4,'c5_5,'c5_11, 'c6_8) adder
  *('c5_6,'c5_7, 'c5_8, 'c5_12, 'c6_9) adder
  *('c5_9,'c5_10, 'c5_11, 'c5_13, 'c6_10) adder
  *('c5_12,'c5_13, _ z, 'c5, 'c6_11) adder
    
  *('c6_0,'c6_1,'c6_2,'c6_12, _ ) adder * ('c6_3,'c6_4,'c6_5,'c6_13, _ ) adder
  *('c6_6,'c6_7, 'c6_8, 'c6_14, _ ) adder
  *('c6_9,'c6_10, 'c6_11, 'c6_15, _) adder
  *('c6_12,'c6_13, 'c6_14, 'c6_16, _ ) adder
  *('c6_15,'c6_16, _ z, 'c6, _ ) adder

  * ('c3_r,'c3, 'c3_r2,'c3_f1) cloner2 * ('c3_r2,'c3_f2,'c3_f3) cloner

  * (_ o, 'c3_f1, 'c4, 'eq1) eq_chain * ('eq1, 'c3_f2,'c5,'eq2) eq_chain
  * ('eq2, 'c3_f3,'c6,'eq3) eq_chain

  * ('eq3,'o3) flip

  * ('oa,'ob,'o4) or_ * ('o3, 'o4,'overflow) or_

  -> < b0:'a0; b1:'a1; b2:'a2; s:'sa; overflow:'oa > t
  -> < b0:'b0; b1:'b1; b2:'b2; s:'sb; overflow:'ob > t
  -> < b0:'c0; b1:'c1; b2:'c2; s:'c3; overflow:'overflow > t
= fun _ x y -> N.create @@ N.to_int x * N.to_int y
 
let mult k l =
  mult (
    Cloner2, Cloner2, Cloner2,
    Cloner2, Cloner2, Cloner,
    Cloner2, Cloner2,
    Cloner2, Cloner2,
    Cloner2, Cloner,
    Cloner2,

    Cloner2, Cloner2, Cloner2,
    Cloner2, Cloner2, Cloner,
    Cloner2, Cloner2,
    Cloner2, Cloner2,
    Cloner2, Cloner,
    Cloner2,
    
    Mult,Mult,Mult,Mult,Mult,Mult,Mult,
    Mult,Mult,Mult,Mult,Mult,Mult,
    Mult,Mult,Mult,Mult,Mult,
    Mult,Mult,Mult,Mult,
    Mult,Mult,Mult,
    Mult,Mult,
    Mult,

    Adder,
    Adder,Adder,
    Adder,Adder,Adder,
    Adder,Adder,Adder,Adder,
    Adder,Adder,Adder,Adder,Adder,
    Adder,Adder,Adder,Adder,Adder,Adder,

    Cloner2,Cloner,

    Eqc,Eqc,Eqc,

    Flip,

    Or,Or
  )
    k l

module Ops = struct
  let ( + ) x y = add x y
  let ( - ) x y = minus x y
  let ( ~- ) x = uminus x
  let ( * ) k l = mult k l
end

