module N = Natural
module L = Logic_gates
module Int = Integer
module A = Opt_integer_ops

type +'a t = 'num Int.t * 'div Int.t
  constraint
    'a = < num: 'num; div: 'div >
;;


let frac: 'a Int.t -> 'b Int.t -> <num:'a;div:'b> t =
  fun x y -> x,y

let num (a,b : 'a t) = a
let div (a,b : 'a t) = b
  

let transmute : 'a t -> 'b t = fun (x,y) -> N.(transmute x, transmute y)
let duplicate : 'a t -> 'b t * 'c t = fun (x,y) ->
  let x,x' = Int.duplicate x
  and y, y' = Int.duplicate y in
  frac x y, frac x' y'


let if_ :('a,'b,'c,'r) L.if_ -> 'a N.t -> 'b t -> 'c t -> 'r t =
  fun _ a b c ->
    if N.to_int a = 0 then transmute b else transmute c
        
let if_ a b = if_ L.If a b

let uminus (a,b : 'a t) = frac (A.uminus a) b 

let add x y =
  let num1, num1' = Int.duplicate @@ num x in
  let num2, num2' = Int.duplicate @@ num y in
  let div1_t, div1',div1_r = Int.duplicate2 @@ div x in
  let div2_t, div2', div2'' = Int.duplicate2 @@ div y in
  let div1'',div1''' = Int.duplicate div1_r in
 let best = frac A.Ops.( num1 + num2) div1' in
 let gen = frac A.Ops.( num1' * div2'' + num2' * div1''') A.Ops.(div1'' * div2' )
  in
  let test = Int.eq div1_t div2_t in
  if_ test best gen

let minus x y = add x @@ uminus y

let mult (a,b : 'a t) (c,d: 'b t) = frac A.Ops.(a*c) A.Ops.(b*d)
let inv (a,b : 'a t ) = frac b a
let div x y = mult x @@ inv y

let eq (num_x,div_x) (num_y,div_y) =
  let l, r = A.Ops.( num_x * div_y, num_y * div_x ) (*todo : 2n bits operation *) in
  Int.( eq l r )

module Eq = struct
type absurd
type +'a proof = Proof constraint 'a = 'x * 'y 
let convert: ('a * 'b) proof -> 'a t -> 'b t = fun _ x -> transmute x
let transmute: 'a proof -> 'b proof  = fun eq -> Proof 

let if_ :('a, absurd*absurd,'b, 'r) L.if_ -> 'a N.t -> 'b proof  -> 'r proof =
  fun _ a b -> Proof

let if_ x y = if_ L.If x y

let mk_proof x y  =
  let (x:'a t), (num_x,div_x) = duplicate x
  and (y:' b t), (num_y,div_y) = duplicate y in     
  let l, r = A.Ops.( num_x * div_y, num_y * div_x ) (*todo : 2n bits operation *) in
  let test = Int.( eq l r ) in
  if_ test
    ( Proof: ('a * 'b) proof )
end
let ( %->% ) x y = let open Eq in
  convert (mk_proof x y) x


module Ops = struct
  
  let ( + ) x y = add x y
  let ( ~- ) x = uminus x      
  let ( - ) x y = minus x y
      
  let ( * ) x y = mult x y       
  let ( ~/ ) x = inv x
  let ( / ) x y = div x y

  let ( // ) x y = frac x y
      
end
