module N = Natural
module L = Logic_gates
open L

let one: 'a o N.t = N.create 1
let zero: 'a z N.t = N.create 0    

let one': 'a o N.t = N.create 1
let zero': 'a z N.t = N.create 0    

let one'': 'a o N.t = N.create 1
let zero'': 'a z N.t = N.create 0    


let or_ : ('a,'b,'c) g_or -> 'a N.t -> 'b N.t -> 'c N.t =
  fun _ x y ->N.( create @@ to_int x lor to_int y )

let t =
  or_ L.Or one zero
    
let eq: ('c,'x,'y,'eq) eq_chain -> 'c N.t -> 'x N.t -> 'y N.t -> 'eq N.t =
  fun _ c x y ->
    N.( create @@ if (to_int c =0) && to_int x= to_int y then 1 else 0 )

let eq x y= eq L.Eqc x y
    
let eq_test =
  eq one one' one''

