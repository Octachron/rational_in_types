open Fraction
module I = struct
  open Integer
  open Opt_integer_ops    
  let zero = z
  let one = one
  let two = lsl_1 one
  let four = lsl_1 two
  let o1, o2, o3 = Int.duplicate2 one
end
open Ops
let one = I.o1 // I.o2
let m_one = -one
let (o1, o2) = duplicate one
let m_one' = one * m_one

let m_one' = if_ (N.create 1 : _ Logic_gates.o N.t ) one m_one
    
let two = o1 + o2

let three = two + one
let six = two * three            

let half = inv two
let third = inv three
let sixth, sixth' = duplicate @@ inv six

let one'' = two * half
let third' = sixth + sixth'            
let third'' = one'' %->% one
