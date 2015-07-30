type +'a t = private int

val create : int -> 'a t
val to_int : 'a t -> int
val transmute : 'a t -> 'b t

type polycreate = { f: 'a. int -> 'a t }
val polycreate : polycreate  

type polytransmute = { t: 'a 'b. 'a t -> 'b t }
val polytransmute : polytransmute
