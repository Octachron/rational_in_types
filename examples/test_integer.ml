open Handwritten_integer3_opt
let (o1, o2, o3) = duplicate2 one
    
let two' = add o1 o2

let z' = add m_one one
let (z1, z2) = duplicate z

let two = lsl_1 o1

let one''  =
  assert_no_overflow @@
  let one, o1, o_r = duplicate2 one in
  let o2, o3 = duplicate o_r in
  Ops.( o3 + o2 + one - lsl_1 o1 )
    
let one =
  Ops.( o1 * o2)

let two'' = Ops.( o1 * two)
         
let m_one'= Ops.( one * m_one )
let one''' =
  Ops.( m_one * m_one' )
let m_seven =
  let a, b  = duplicate two in
  Ops.( ((a + one) * b + one ) * m_one )

let overflow = Ops.( m_seven * two )
