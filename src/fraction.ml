module N = Natural
module L = Logic_gates

type 'a t = 'num N.t * 'div N.t
  constraint
    'a = < num: 'num; div: 'div >
