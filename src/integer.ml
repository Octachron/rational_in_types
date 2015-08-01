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

type ('a,'b,'c) duplicater = Nil_duplicater

let mk_duplicater:
 ('o0,'o1,'o2) cloner * ('b0_0,'b0_1,'b0_2) cloner
  * ('b1_0,'b1_1,'b1_2) cloner * ('b2_0,'b2_1,'b2_2) cloner
  * ('s0,'s1,'s2) cloner
  -> (
    < b0:'b0_0; b1: 'b1_0; b2: 'b2_0; s:'s0; overflow:'o0>,
    < b0:'b0_1; b1: 'b1_1; b2: 'b2_1; s:'s1; overflow:'o1>,
    < b0:'b0_2; b1: 'b1_2; b2: 'b2_2; s:'s2; overflow:'o2>
  ) duplicater = fun _ -> Nil_duplicater

let mk_duplicater () =  mk_duplicater @@ L.(Cloner,Cloner,Cloner,Cloner,Cloner) 

let duplicate:
  ('a,'b,'c) duplicater 
  -> 'a t
  -> 'b t * 'c t =
  fun _ x -> N.(polytransmute.t x, polytransmute.t x)                              

let duplicate x =
  duplicate (mk_duplicater () ) x

let duplicate :  < b0 : [< `_0 of
            'a L.z * 'b L.z &
            'c * 'd
        | `_1 of
            'a L.o * 'b L.o &
            'c * 'd];
  b1 : [< `_0 of
            'u L.z * 'v L.z &
            'w * 'x
        | `_1 of
            'u L.o * 'v L.o &
            'w * 'x];
  b2 : [< `_0 of
            'o1 L.z * 'p1 L.z &
            'q1 * 'r1
        | `_1 of
            'o1 L.o * 'p1 L.o &
            'q1 * 'r1];
  overflow : [< `_0 of
                  'i2 L.z * 'j2 L.z &
                  'k2 * 'l2
             | `_1 of
                  'i2 L.o * 'j2 L.o &
                  'k2 * 'l2];
  s : [< `_0 of
           'c3 L.z * 'd3 L.z &
           'e3 * 'f3
      | `_1 of
           'c3 L.o * 'd3 L.o &
           'e3 * 'f3] >
t ->
< b0 : 'c; b1 : 'w; b2 : 'q1; overflow : 'k2; s : 'e3 > t *
< b0 : 'd; b1 : 'x; b2 : 'r1; overflow : 'l2; s : 'f3 > t =
  fun x -> N.(transmute x, transmute x)

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
  -> < b0:'b0_0; b1: 'b1_0; b2: 'b2_0; s: 's0; overflow:_ z> t
  -> < b0:'b0_1; b1: 'b1_1; b2: 'b2_1; s: 's1; overflow:_ z> t
  -> < b0:'b0_2; b1: 'b1_2; b2: 'b2_2; s: 's2; overflow:'overflow> t =
  fun _ x y -> N.( create @@ to_int x + to_int y)                             

let add x y =
  add (Adder,Adder,Adder,Overflow) x y

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
  (* First we extend the two argument by copying the sign bits *)
  ('a3_r,'a3_r2,'a3,'a4) cloner2 * ('a3_r2,'a5,'a6) cloner
  * ('b3_r, 'b3_r2,'b3,'b4) cloner2 * ('b3_r2,'b5,'b6) cloner

(*First stage : multiplication by b0 *)
(* First if b0 = 1, we need to 1) clone the relevant a bits then add to then to the current sums *)
  * ('a0, 'a0_0,'a0_r0,'a0_r1) cloner2 * ('a1, 'a1_0,'a1_r0,'a1_r1) cloner2
  * ('a2, 'a2_0,'a2_1,'a2_r1) cloner2 * ('a3, 'a3_0,'a3_1,'a3_r1) cloner2
  * ('a4, 'a4_0,'a4_1,'a4_2) cloner2 * ('a5, 'a5_0,'a5_1) cloner

  * ( 'b0,
      _ z   * _ z   * _ z   * _ z   * _ z   * _ z   * _ z,
      'a0_0 * 'a1_0 * 'a2_0 * 'a3_0 * 'a4_0 * 'a5_0 * 'a6,
      'c0   * 'c1_r * 'c2_r * 'c3_r * 'c4_r * 'c5_r * 'c6_r )
    if_
    
(* Second stage: more duplication of a *)
  *  ('a0_r0, 'a0_1,'a0_2,'a0_3) cloner2 * ('a1_r0, 'a1_1,'a1_2,'a1_3) cloner2
  * ('a2_r1, 'a2_2,'a2_3,'a2_4) cloner2 * ('a3_r1, 'a3_2,'a3_3) cloner

    (* Cloning previous result*)
  * ('c1_r, 'c1_0,'c1_b) cloner * ('c2_r, 'c2_0,'c2_b) cloner
  * ('c3_r, 'c3_0,'c3_b) cloner * ('c4_r, 'c4_0,'c4_b) cloner
  * ('c5_r, 'c5_0,'c5_b) cloner * ('c6_r, 'c6_0,'c6_b) cloner
    
(* addition for the b1=1 branch *)
  * ('c1_0,'a0_1,_ z, 's1, 'i0_1) adder * ('c2_0,'a1_1,'i0_1, 's2, 'i0_2 ) adder
  * ('c3_0,'a2_1,'i0_2, 's3, 'i0_3) adder * ('c4_0,'a3_1,'i0_3, 's4, 'i0_4) adder
  * ('c5_0,'a4_1,'i0_4, 's5, 'i0_5) adder * ('c6_0,'a5_1,'i0_5, 's6 , _ ) adder

(*if b1=1 *)
  *  ( 'b1,
       'c1_b * 'c2_b  * 'c3_b  * 'c4_b  * 'c5_b  * 'c6_b,
       's1   * 's2    * 's3    * 's4    * 's5    * 's6,
       'c1   * 'c2_r1 * 'c3_r1 * 'c4_r1 * 'c5_r1 * 'c6_r1
     ) if_
(* Third stage: last duplication of a *)
  * ('a0_r1, 'a0_4,'a0_5,'a0_6) cloner2 * ('a1_r1, 'a1_4,'a1_5) cloner

    (* Cloning previous result*)
  * ('c2_r1, 'c2_1,'c2_1b) cloner * ('c3_r1, 'c3_1,'c3_1b) cloner
  * ('c4_r1, 'c4_1,'c4_1b) cloner * ('c5_r1, 'c5_1,'c5_1b) cloner
  * ('c6_r1, 'c6_1,'c6_1b) cloner
    
(* addition for the b2=1 branch *)
  * ('c2_1,'a0_2,  _ z, 's2_1, 'i1_1) adder * ('c3_1,'a1_2,'i1_1, 's3_1, 'i1_2) adder
  * ('c4_1,'a2_2,'i1_2, 's4_1, 'i1_3) adder * ('c5_1,'a3_2,'i1_3, 's5_1, 'i1_4) adder
  * ('c6_1,'a4_2,'i1_4, 's6_1, 'i1_5) adder

(*if b2=1 *)
  *  ( 'b2,
       'c2_1b * 'c3_1b * 'c4_1b * 'c5_1b * 'c6_1b,
       's2_1  * 's3_1  * 's4_1  * 's5_1  * 's6_1,
       'c2    * 'c3_r2 * 'c4_r2 * 'c5_r2 * 'c6_r2
     ) if_
    
(* Fourth stage *)

    (* Cloning previous result*)
  * ('c3_r2, 'c3_2,'c3_2b) cloner * ('c4_r2, 'c4_2,'c4_2b) cloner
  * ('c5_r2, 'c5_2,'c5_2b) cloner * ('c6_r2, 'c6_2,'c6_2b) cloner
    
(* addition for the b3=1 branch *)
  * ('c3_2,'a0_3,  _ z, 's3_2, 'i2_1) adder * ('c4_2,'a1_3,'i2_1, 's4_2, 'i2_2) adder
  * ('c5_2,'a2_3,'i2_2, 's5_2, 'i2_3) adder * ('c6_2,'a3_3,'i2_3, 's6_2, _ ) adder

(*if b3=1 *)
  *  ( 'b3,
       'c3_2b * 'c4_2b * 'c5_2b * 'c6_2b,
       's3_2  * 's4_2  * 's5_2  * 's6_2,
       'c3    * 'c4_r3 * 'c5_r3 * 'c6_r3
     ) if_
  
(* Fifth stage *)
    (* Cloning previous result*)
  * ('c4_r3, 'c4_3,'c4_3b) cloner * ('c5_r3, 'c5_3,'c5_3b) cloner
  * ('c6_r3, 'c6_3,'c6_3b) cloner
    
(* addition for the b4=1 branch *)
  * ('c4_3,'a0_4,  _ z, 's4_3, 'i3_1) adder * ('c5_3,'a1_4,'i3_1, 's5_3, 'i3_2) adder
  * ('c6_3,'a2_4,'i3_2, 's6_3, 'i3_3) adder

(*if b4=1 *)
  *  ( 'b4,
       'c4_3b * 'c5_3b * 'c6_3b,
       's4_3  * 's5_3  * 's6_3,
       'c4    * 'c5_r4 * 'c6_r4
     ) if_

(* Sixth stage *)
    (* Cloning previous result*)
  * ('c5_r4, 'c5_4,'c5_4b) cloner * ('c6_r4, 'c6_4,'c6_4b) cloner
    
(* addition for the b5=1 branch *)
  * ('c5_4,'a0_5,  _ z, 's5_4, 'i4_1) adder * ('c6_4,'a1_5,'i4_1, 's6_4, _ ) adder

(*if b5=1 *)
  *  ( 'b5,
       'c5_4b * 'c6_4b,
       's5_4  * 's6_4,
       'c5    * 'c6_r5
     ) if_

(* Last stage *)
    (* Cloning previous result*)
  * ('c6_r5, 'c6_5,'c6_5b) cloner
    
(* addition for the b6=1 branch *)
  * ('c6_5,'a0_6,  _ z, 's6_5, _ ) adder
(*if b6=1 *)
  *  ( 'b6, 'c6_5b, 's6_5, 'c6 ) if_

  (* Overflow test *)
  * ('c3, 'sc , 'c3_ro) cloner * ('c3_ro, 'o4 , 'o5, 'o6) cloner2
  * (_ o, 'o4, 'c4, 'eq1) eq_chain * ('eq1, 'o5,'c5,'eq2) eq_chain
  * ('eq2, 'o6,'c6,'eq3) eq_chain

  * ('eq3,'overflow) flip

  -> < b0:'a0; b1:'a1; b2:'a2; s:'a3_r; overflow: _ z > t
  -> < b0:'b0; b1:'b1; b2:'b2; s:'b3_r; overflow: _ z > t
  -> < b0:'c0; b1:'c1; b2:'c2; s:'sc; overflow:'overflow > t
= fun _ x y -> N.create @@ N.to_int x * N.to_int y

let mgate= (
  Cloner2, Cloner, Cloner2, Cloner,

  (*S 1*)
  Cloner2, Cloner2, Cloner2, Cloner2, Cloner2, Cloner,
  If,

    (*S 2 *)
  Cloner2, Cloner2, Cloner2, Cloner,
  Cloner, Cloner, Cloner, Cloner, Cloner, Cloner,
  Adder, Adder, Adder, Adder, Adder, Adder,
  If,
  
  (*S 3 *)
  Cloner2, Cloner,
  Cloner, Cloner, Cloner, Cloner, Cloner,
  Adder, Adder, Adder, Adder, Adder,
  If,
  (*S 4 *)
  Cloner, Cloner, Cloner, Cloner,
  Adder, Adder, Adder, Adder,
  If,
  
  (*S 5 *)
  Cloner, Cloner, Cloner,
  Adder, Adder, Adder,
  If,

  (*S 6 *)
  Cloner, Cloner,
  Adder, Adder,
  If,
    
  (*S 7 *)
  Cloner,
  Adder,
  If,

  
  (*Overflow*)
  Cloner,Cloner2,
  Eqc,Eqc,Eqc,
  Flip
)

let mult x y= mult mgate x y

module Ops = struct
  let ( + ) x y = add x y
  let ( - ) x y = minus x y
  let ( ~- ) x = uminus x
  let ( * ) k l = mult k l
end
