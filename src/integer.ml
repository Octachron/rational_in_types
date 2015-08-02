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
