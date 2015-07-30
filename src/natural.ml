type 'a t =int
let create n = n
let to_int n = n
let transmute n = n

type polycreate = { f: 'a. int -> 'a t }
let polycreate = { f = create }  

type polytransmute = { t: 'a. int -> 'a t }
let polytransmute = { t = transmute }  
