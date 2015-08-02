module N = Natural
open Logic_gates
open Integer

let add: < b0 : [< `_0 of
            [< `_0 of
                 ('b *
                  ([< `_0 of
                        'd *
                        ([< `_0 of
                              'f *
                              ([< `_0 of 'h * 'i | `_1 of 'h * 'i ] as 'g)
                          | `_1 of 'f * 'g ]
                         as 'e)
                    | `_1 of 'd * 'e ]
                   as 'c))
                 L.z
             | `_1 of ('b * 'c) L.z ]
            as 'a &
            [< `_0 of [< `_0 of 'j L.z * 'k L.z | `_1 of 'j L.o * 'k L.z ]
             | `_1 of [< `_0 of 'j L.o * 'k L.z | `_1 of 'j L.z * 'k L.o ] ] 
        | `_1 of
            'a &
            [< `_0 of [< `_0 of 'j L.o * 'k L.z | `_1 of 'j L.z * 'k L.o ]
             | `_1 of [< `_0 of 'j L.z * 'k L.o | `_1 of 'j L.o * 'k L.o ] ] ];
  b1 : [< `_0 of
            [< `_0 of 'c | `_1 of 'c ] as 'x &
            [< `_0 of [< `_0 of 'y L.z * 'z L.z | `_1 of 'y L.o * 'z L.z ]
             | `_1 of [< `_0 of 'y L.o * 'z L.z | `_1 of 'y L.z * 'z L.o ] ]
        | `_1 of
            'x &
            [< `_0 of [< `_0 of 'y L.o * 'z L.z | `_1 of 'y L.z * 'z L.o ]
             | `_1 of [< `_0 of 'y L.z * 'z L.o | `_1 of 'y L.o * 'z L.o ] ] ];
  b2 : [< `_0 of
            [< `_0 of 'e | `_1 of 'e ] as 'm1 &
            [< `_0 of
                 [< `_0 of 'n1 L.z * 'o1 L.z | `_1 of 'n1 L.o * 'o1 L.z ]
             | `_1 of
                 [< `_0 of 'n1 L.o * 'o1 L.z | `_1 of 'n1 L.z * 'o1 L.o ] ]
        | `_1 of
            'm1 &
            [< `_0 of
                 [< `_0 of 'n1 L.o * 'o1 L.z | `_1 of 'n1 L.z * 'o1 L.o ]
             | `_1 of
                 [< `_0 of 'n1 L.z * 'o1 L.o | `_1 of 'n1 L.o * 'o1 L.o ] ] ];
  overflow : 'b2 L.z;
  s : [< `_0 of
           [< `_0 of [< `_0 of 'c2 L.z * 'd2 L.z | `_1 of 'c2 L.o * 'd2 L.o ]
            | `_1 of
                [< `_0 of 'c2 L.o * 'd2 L.z | `_1 of 'c2 L.z * 'd2 L.z ]
                as 'no_overflow ] &
           [< `_0 of 'g | `_1 of 'g ] as 'e2 
       | `_1 of
           [< `_0 of 'no_overflow
            | `_1 of [< `_0 of 'c2 L.o * 'd2 L.z | `_1 of 'c2 L.z * 'd2 L.o ] ] &
           'e2 ]>
t ->
< b0 : 'a; b1 : 'x; b2 : 'm1; overflow : 'r2 L.z; s : 'e2 > t ->
  < b0 : 'b; b1 : 'd; b2 : 'f; overflow : 'i; s : 'h > t =
  fun x y -> N.(create @@ to_int x + to_int y)

let flip :
< b0 : [< `_0 of [ `_1 of 'a ] & 'b
       | `_1 of [ `_0 of 'a ] & 'b
       ];
  b1 : [< `_0 of [ `_1 of 'i ] & 'j
        | `_1 of
            [ `_0 of 'i ] & 'j ];
  b2 : [< `_0 of
            [ `_1 of 'q ] & 'r
       | `_1 of [ `_0 of 'q ] & 'r
       ];
  overflow : 'y;
  s : [< `_0 of [ `_1 of 'z ] & 'a1
      | `_1 of [ `_0 of 'z ] & 'a1 ] > t
-> < b0 : 'b; b1 : 'j; b2 : 'r; overflow : 'y; s : 'a1 > t
= fun x -> N.( create @@ -(to_int x + 1) )

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

< b0 : [< `_0 of
            'a L.z * 'b L.z * 'c L.z &
            'd *
            ([< `_0 of
                  'f L.z * 'g L.z * 'h L.z &
                  ([< `_0 of
                        ('j *
                         ([< `_0 of
                               'l *
                               ([< `_0 of
                                     'n *
                                     ([< `_0 of
                                           'p *
                                           ([< `_0 of
                                                 'r *
                                                 ([< `_0 of 't * 'u
                                                   | `_1 of 't * 'u ]
                                                  as 's)
                                             | `_1 of 'r * 's ]
                                            as 'q)
                                       | `_1 of 'p * 'q ]
                                      as 'o)
                                 | `_1 of 'n * 'o ]
                                as 'm)
                           | `_1 of 'l * 'm ]
                          as 'k))
                        L.z
                    | `_1 of ('j * 'k) L.z ]
                   as 'i) *
                  ([< `_0 of
                        ('w *
                         ([< `_0 of
                               'y *
                               ([< `_0 of
                                     'a1 *
                                     ([< `_0 of
                                           'c1 *
                                           ([< `_0 of 'e1 * 'f1
                                             | `_1 of 'e1 * 'f1 ]
                                            as 'd1)
                                       | `_1 of 'c1 * 'd1 ]
                                      as 'b1)
                                 | `_1 of 'a1 * 'b1 ]
                                as 'z)
                           | `_1 of 'y * 'z ]
                          as 'x))
                        L.z
                    | `_1 of ('w * 'x) L.z ]
                   as 'v) *
                  ([< `_0 of
                        ('h1 *
                         ([< `_0 of
                               'j1 *
                               ([< `_0 of
                                     'l1 *
                                     ([< `_0 of 'n1 * 'o1 | `_1 of 'n1 * 'o1 ]
                                      as 'm1)
                                 | `_1 of 'l1 * 'm1 ]
                                as 'k1)
                           | `_1 of 'j1 * 'k1 ]
                          as 'i1))
                        L.z
                    | `_1 of ('h1 * 'i1) L.z ]
                   as 'g1) &
                  'p1 L.z * 'q1 L.z * 'r1 L.z 
              | `_1 of
                  'f L.o * 'g L.o * 'h L.o &
                  'i * 'v * 'g1  ]
             as 'e) *
            ([< `_0 of
                  'i2 L.z * 'j2 L.z * 'k2 L.z &
                  ([< `_0 of
                        ('m2 *
                         ([< `_0 of
                               'o2 *
                               ([< `_0 of 'q2 * 'r2 | `_1 of 'q2 * 'r2 ]
                                as 'p2)
                           | `_1 of 'o2 * 'p2 ]
                          as 'n2))
                        L.z
                    | `_1 of ('m2 * 'n2) L.z ]
                   as 'l2) *
                  ([< `_0 of
                        ('t2 *
                         ([< `_0 of 'v2 * 'w2 | `_1 of 'v2 * 'w2 ] as 'u2))
                        L.z
                    | `_1 of ('t2 * 'u2) L.z ]
                   as 's2) *
                  ([< `_0 of ('y2 * 'a3) L.z | `_1 of ('y2 * 'a3) L.z ]
                   as 'x2) &
                  'b3 L.z * 'c3 L.z * 'd3 L.z
              | `_1 of
                  'i2 L.o * 'j2 L.o * 'k2 L.o &
                  'l2 * 's2 * 'x2 ]
             as 'h2) &
            't3 L.z * 'u3 L.z * 'v3 L.z
        | `_1 of
            'a L.o * 'b L.o * 'c L.o &
            'd * 'e * 'h2 ];
  b1 : [< `_0 of
            'l4 L.z * 'm4 L.z * 'n4 L.z &
            'o4 *
            ([< `_0 of
                  'q4 L.z * 'r4 L.z * 's4 L.z &
                  ([< `_0 of 'k | `_1 of 'k ] as 't4) *
                  ([< `_0 of 'x | `_1 of 'x ] as 'u4) *
                  ([< `_0 of 'i1 | `_1 of 'i1 ] as 'v4)
              | `_1 of
                  'q4 L.o * 'r4 L.o * 's4 L.o &
                  't4 * 'u4 * 'v4 ]
             as 'p4) *
            ([< `_0 of
                  'p5 L.z * 'q5 L.z &
                  ([< `_0 of 'n2 | `_1 of 'n2 ] as 'r5) *
                  ([< `_0 of 'u2 | `_1 of 'u2 ] as 's5)
              | `_1 of
                  'p5 L.o * 'q5 L.o &
                  'r5 * 's5 ]
             as 'o5) &
            'f6 L.z * 'g6 L.z * 'h6 L.z
        | `_1 of
            'l4 L.o * 'm4 L.o * 'n4 L.o &
            'o4 * 'p4 * 'o5];
  b2 : [< `_0 of
            'x6 L.z * 'y6 L.z * 'z6 L.z &
            'a7 * ([< `_0 of 'm | `_1 of 'm ] as 'b7) *
            ([< `_0 of
                  'd7 L.z * 'e7 L.z * 'f7 L.z &
                  ([< `_0 of 'z | `_1 of 'z ] as 'g7) *
                  ([< `_0 of 'k1 | `_1 of 'k1 ] as 'h7) *
                  ([< `_0 of 'p2 | `_1 of 'p2 ] as 'i7)
              | `_1 of
                  'd7 L.o * 'e7 L.o * 'f7 L.o &
                  'g7 * 'h7 * 'i7 ]
             as 'c7)
        | `_1 of
            'x6 L.o * 'y6 L.o * 'z6 L.o &
            'a7 * 'b7 * 'c7 ];
  overflow : 't8 L.z;
  s : [< `_0 of
           'u8 L.z * 'v8 L.z * 'w8 L.z &
           ([< `_0 of
                 'y8 L.z * 'z8 L.z &
                 ([< `_0 of
                       'b9 L.z * 'c9 L.z &
                       'd9 * ([< `_0 of 's | `_1 of 's ] as 'e9)
                   | `_1 of
                       'b9 L.o * 'c9 L.o &
                       'd9 * 'e9 ]
                  as 'a9) *
                 'r9 &
                 's9 L.z * 't9 L.z
             | `_1 of
                 'y8 L.o * 'z8 L.o &
                 'a9 * 'r9 ]
            as 'x8) *
           ([< `_0 of
                 'f10 L.z * 'g10 L.z * 'h10 L.z &
                 'i10 * ([< `_0 of 'o | `_1 of 'o ] as 'j10) *
                 ([< `_0 of
                       'l10 L.z * 'm10 L.z &
                       ([< `_0 of 'b1 | `_1 of 'b1 ] as 'n10) *
                       ([< `_0 of 'm1 | `_1 of 'm1 ] as 'o10)
                   | `_1 of
                       'l10 L.o * 'm10 L.o &
                       'n10 * 'o10 ]
                  as 'k10) &
                 'b11 L.z * 'c11 L.z * 'd11 L.z
             | `_1 of
                 'f10 L.o * 'g10 L.o * 'h10 L.o &
                 'i10 * 'j10 * 'k10 ]
            as 'e10) *
           ([< `_0 of
                 'u11 L.z * 'v11 L.z * 'w11 L.z &
                 'x11 * ([< `_0 of 'q | `_1 of 'q ] as 'y11) *
                 ([< `_0 of 'd1 | `_1 of 'd1 ] as 'z11)
             | `_1 of
                 'u11 L.o * 'v11 L.o * 'w11 L.o &
                 'x11 * 'y11 * 'z11 ]
            as 't11) &
           's12 L.z * 't12 L.z * 'u12 L.z &
           'v12 L.z * 'w12 L.z * 'x12 L.z
       | `_1 of
           'u8 L.o * 'v8 L.o * 'w8 L.o &
           'x8 * 'e10 * 't11 ] >
t
->  < b0 : [< `_0 of
            'k13 L.z * 'l13 L.z * 'm13 L.z * 'n13 L.z * 'o13 L.z * 'p13 L.z *
            'q13 L.z &
            'r13 *
            ([< `_0 of
                  't13 L.z * 'u13 L.z &
                  ([< `_0 of
                        'i &
                        [< `_0 of
                             [< `_0 of 'w13 L.z * 'x13 L.z
                              | `_1 of 'w13 L.o * 'x13 L.z ]
                         | `_1 of
                             [< `_0 of 'w13 L.o * 'x13 L.z
                              | `_1 of 'w13 L.z * 'x13 L.o ] ]  
                    | `_1 of
                        'i &
                        [< `_0 of
                             [< `_0 of 'w13 L.o * 'x13 L.z
                              | `_1 of 'w13 L.z * 'x13 L.o ]
                         | `_1 of
                             [< `_0 of 'w13 L.z * 'x13 L.o
                              | `_1 of 'w13 L.o * 'x13 L.o ] ] ]
                   as 'v13) *
                  'k14 &
                  'l14 L.z * 'm14 L.z 
              | `_1 of
                  't13 L.o * 'u13 L.o &
                  'v13 * 'k14 ]
             as 's13) *
            ([< `_0 of
                  'y14 L.z * 'z14 L.z &
                  ([< `_0 of
                        't4 &
                        [< `_0 of
                             [< `_0 of 'b15 L.z * 'c15 L.z
                              | `_1 of 'b15 L.o * 'c15 L.z ]
                         | `_1 of
                             [< `_0 of 'b15 L.o * 'c15 L.z
                              | `_1 of 'b15 L.z * 'c15 L.o ] ]
                    | `_1 of
                        't4 &
                        [< `_0 of
                             [< `_0 of 'b15 L.o * 'c15 L.z
                              | `_1 of 'b15 L.z * 'c15 L.o ]
                         | `_1 of
                             [< `_0 of 'b15 L.z * 'c15 L.o
                              | `_1 of 'b15 L.o * 'c15 L.o ] ]
                         ]
                   as 'a15) *
                  'p15 &
                  'q15 L.z * 'r15 L.z
              | `_1 of
                  'y14 L.o * 'z14 L.o &
                  'a15 * 'p15 ]
             as 'x14) *
            ([< `_0 of
                  'd16 L.z * 'e16 L.z &
                  ([< `_0 of
                        'b7 &
                        [< `_0 of
                             [< `_0 of 'g16 L.z * 'h16 L.z
                              | `_1 of 'g16 L.o * 'h16 L.z ]
                         | `_1 of
                             [< `_0 of 'g16 L.o * 'h16 L.z
                              | `_1 of 'g16 L.z * 'h16 L.o ] ]
                    | `_1 of
                        'b7 &
                        [< `_0 of
                             [< `_0 of 'g16 L.o * 'h16 L.z
                              | `_1 of 'g16 L.z * 'h16 L.o ]
                         | `_1 of
                             [< `_0 of 'g16 L.z * 'h16 L.o
                              | `_1 of 'g16 L.o * 'h16 L.o ] ] ]
                   as 'f16) *
                  'u16 &
                  'v16 L.z * 'w16 L.z
              | `_1 of
                  'd16 L.o * 'e16 L.o &
                  'f16 * 'u16 ]
             as 'c16) *
            ([< `_0 of
                  'i17 L.z * 'j17 L.z &
                  ([< `_0 of
                        'j10 &
                        [< `_0 of
                             [< `_0 of 'l17 L.z * 'm17 L.z
                              | `_1 of 'l17 L.o * 'm17 L.z ]
                         | `_1 of
                             [< `_0 of 'l17 L.o * 'm17 L.z
                              | `_1 of 'l17 L.z * 'm17 L.o ] ] 
                    | `_1 of
                        'j10 &
                        [< `_0 of
                             [< `_0 of 'l17 L.o * 'm17 L.z
                              | `_1 of 'l17 L.z * 'm17 L.o ]
                         | `_1 of
                             [< `_0 of 'l17 L.z * 'm17 L.o
                              | `_1 of 'l17 L.o * 'm17 L.o ] ] ]
                   as 'k17) *
                  'z17 &
                  'a18 L.z * 'b18 L.z 
              | `_1 of
                  'i17 L.o * 'j17 L.o &
                  'k17 * 'z17 ]
             as 'h17) *
            ([< `_0 of
                  'n18 L.z * 'o18 L.z &
                  ([< `_0 of
                        'y11 &
                        [< `_0 of
                             [< `_0 of 'q18 L.z * 'r18 L.z
                              | `_1 of 'q18 L.o * 'r18 L.z ]
                         | `_1 of
                             [< `_0 of 'q18 L.o * 'r18 L.z
                              | `_1 of 'q18 L.z * 'r18 L.o ] ]
                    | `_1 of
                        'y11 &
                        [< `_0 of
                             [< `_0 of 'q18 L.o * 'r18 L.z
                              | `_1 of 'q18 L.z * 'r18 L.o ]
                         | `_1 of
                             [< `_0 of 'q18 L.z * 'r18 L.o
                              | `_1 of 'q18 L.o * 'r18 L.o ] ] ]
                   as 'p18) *
                  'e19 &
                  'f19 L.z * 'g19 L.z
              | `_1 of
                  'n18 L.o * 'o18 L.o &
                  'p18 * 'e19 ]
             as 'm18) *
            ([< `_0 of
                  's19 L.z * 't19 L.z &
                  ([< `_0 of
                        'e9 &
                        [< `_0 of
                             [< `_0 of 'v19 L.z * 'w19 L.z
                              | `_1 of 'v19 L.o * 'w19 L.z ]
                         | `_1 of
                             [< `_0 of 'v19 L.o * 'w19 L.z
                              | `_1 of 'v19 L.z * 'w19 L.o ] ]
                    | `_1 of
                        'e9 &
                        [< `_0 of
                             [< `_0 of 'v19 L.o * 'w19 L.z
                              | `_1 of 'v19 L.z * 'w19 L.o ]
                         | `_1 of
                             [< `_0 of 'v19 L.z * 'w19 L.o
                              | `_1 of 'v19 L.o * 'w19 L.o ] ] ]
                   as 'u19) *
                  'j20 &
                  'k20 L.z * 'l20 L.z
              | `_1 of
                  's19 L.o * 't19 L.o &
                  'u19 * 'j20 ]
             as 'r19)
        | `_1 of
            'd * 'o4 * 'a7 * 'i10 * 'x11 * 'd9 * 'r9 &
            'r13 * 's13 * 'x14 * 'c16 * 'h17 * 'm18 * 'r19 ];
  b1 : [< `_0 of
            'k14 * 'p15 * 'u16 * 'z17 * 'e19 * 'j20 &
            'w20 *
            ([< `_0 of
                  'y20 L.z * 'z20 L.z &
                  ([< `_0 of
                        'v &
                        [< `_0 of
                             [< `_0 of 'b21 L.z * 'c21 L.z
                              | `_1 of 'b21 L.o * 'c21 L.z ]
                         | `_1 of
                             [< `_0 of 'b21 L.o * 'c21 L.z
                              | `_1 of 'b21 L.z * 'c21 L.o ] ]
                    | `_1 of
                        'v &
                        [< `_0 of
                             [< `_0 of 'b21 L.o * 'c21 L.z
                              | `_1 of 'b21 L.z * 'c21 L.o ]
                         | `_1 of
                             [< `_0 of 'b21 L.z * 'c21 L.o
                              | `_1 of 'b21 L.o * 'c21 L.o ] ] ]
                   as 'a21) *
                  'p21 &
                  'q21 L.z * 'r21 L.z
              | `_1 of
                  'y20 L.o * 'z20 L.o &
                  'a21 * 'p21 ]
             as 'x20) *
            ([< `_0 of
                  'd22 L.z * 'e22 L.z &
                  ([< `_0 of
                        'u4 &
                        [< `_0 of
                             [< `_0 of 'g22 L.z * 'h22 L.z
                              | `_1 of 'g22 L.o * 'h22 L.z ]
                         | `_1 of
                             [< `_0 of 'g22 L.o * 'h22 L.z
                              | `_1 of 'g22 L.z * 'h22 L.o ] ]
                    | `_1 of
                        'u4 &
                        [< `_0 of
                             [< `_0 of 'g22 L.o * 'h22 L.z
                              | `_1 of 'g22 L.z * 'h22 L.o ]
                         | `_1 of
                             [< `_0 of 'g22 L.z * 'h22 L.o
                              | `_1 of 'g22 L.o * 'h22 L.o ] ] ]
                   as 'f22) *
                  'u22 &
                  'v22 L.z * 'w22 L.z
              | `_1 of
                  'd22 L.o * 'e22 L.o &
                  'f22 * 'u22 ]
             as 'c22) *
            ([< `_0 of
                  'i23 L.z * 'j23 L.z &
                  ([< `_0 of
                        'g7 &
                        [< `_0 of
                             [< `_0 of 'l23 L.z * 'm23 L.z
                              | `_1 of 'l23 L.o * 'm23 L.z ]
                         | `_1 of
                             [< `_0 of 'l23 L.o * 'm23 L.z
                              | `_1 of 'l23 L.z * 'm23 L.o ] ]
                    | `_1 of
                        'g7 &
                        [< `_0 of
                             [< `_0 of 'l23 L.o * 'm23 L.z
                              | `_1 of 'l23 L.z * 'm23 L.o ]
                         | `_1 of
                             [< `_0 of 'l23 L.z * 'm23 L.o
                              | `_1 of 'l23 L.o * 'm23 L.o ] ] ]
                   as 'k23) *
                  'z23 &
                  'a24 L.z * 'b24 L.z
              | `_1 of
                  'i23 L.o * 'j23 L.o &
                  'k23 * 'z23 ]
             as 'h23) *
            ([< `_0 of
                  'n24 L.z * 'o24 L.z &
                  ([< `_0 of
                        'n10 &
                        [< `_0 of
                             [< `_0 of 'q24 L.z * 'r24 L.z
                              | `_1 of 'q24 L.o * 'r24 L.z ]
                         | `_1 of
                             [< `_0 of 'q24 L.o * 'r24 L.z
                              | `_1 of 'q24 L.z * 'r24 L.o ] ] 
                    | `_1 of
                        'n10 &
                        [< `_0 of
                             [< `_0 of 'q24 L.o * 'r24 L.z
                              | `_1 of 'q24 L.z * 'r24 L.o ]
                         | `_1 of
                             [< `_0 of 'q24 L.z * 'r24 L.o
                              | `_1 of 'q24 L.o * 'r24 L.o ] ]
                      ]
                   as 'p24) *
                  'e25 &
                  'f25 L.z * 'g25 L.z
              | `_1 of
                  'n24 L.o * 'o24 L.o &
                  'p24 * 'e25 ]
             as 'm24) *
            ([< `_0 of
                  's25 L.z * 't25 L.z &
                  ([< `_0 of
                        'z11 &
                        [< `_0 of
                             [< `_0 of 'v25 L.z * 'w25 L.z
                              | `_1 of 'v25 L.o * 'w25 L.z ]
                         | `_1 of
                             [< `_0 of 'v25 L.o * 'w25 L.z
                              | `_1 of 'v25 L.z * 'w25 L.o ] ]
                    | `_1 of
                        'z11 &
                        [< `_0 of
                             [< `_0 of 'v25 L.o * 'w25 L.z
                              | `_1 of 'v25 L.z * 'w25 L.o ]
                         | `_1 of
                             [< `_0 of 'v25 L.z * 'w25 L.o
                              | `_1 of 'v25 L.o * 'w25 L.o ] ] ]
                   as 'u25) *
                  'j26 &
                  'k26 L.z * 'l26 L.z
              | `_1 of
                  's25 L.o * 't25 L.o &
                  'u25 * 'j26 ]
             as 'r25)
        | `_1 of
            'j * 'l * 'n * 'p * 'r * 't &
            'w20 * 'x20 * 'c22 * 'h23 * 'm24 * 'r25 ];
  b2 : [< `_0 of
            'p21 * 'u22 * 'z23 * 'e25 * 'j26 &
            'w26 *
            ([< `_0 of
                  'y26 L.z * 'z26 L.z &
                  ([< `_0 of
                        'g1 &
                        [< `_0 of
                             [< `_0 of 'b27 L.z * 'c27 L.z
                              | `_1 of 'b27 L.o * 'c27 L.z ]
                         | `_1 of
                             [< `_0 of 'b27 L.o * 'c27 L.z
                              | `_1 of 'b27 L.z * 'c27 L.o ] ]
                    | `_1 of
                        'g1 &
                        [< `_0 of
                             [< `_0 of 'b27 L.o * 'c27 L.z
                              | `_1 of 'b27 L.z * 'c27 L.o ]
                         | `_1 of
                             [< `_0 of 'b27 L.z * 'c27 L.o
                              | `_1 of 'b27 L.o * 'c27 L.o ] ] ]
                   as 'a27) *
                  'p27 &
                  'q27 L.z * 'r27 L.z
              | `_1 of
                  'y26 L.o * 'z26 L.o &
                  'a27 * 'p27 ]
             as 'x26) *
            ([< `_0 of
                  'd28 L.z * 'e28 L.z &
                  ([< `_0 of
                        'v4 &
                        [< `_0 of
                             [< `_0 of 'g28 L.z * 'h28 L.z
                              | `_1 of 'g28 L.o * 'h28 L.z ]
                         | `_1 of
                             [< `_0 of 'g28 L.o * 'h28 L.z
                              | `_1 of 'g28 L.z * 'h28 L.o ] ]
                    | `_1 of
                        'v4 &
                        [< `_0 of
                             [< `_0 of 'g28 L.o * 'h28 L.z
                              | `_1 of 'g28 L.z * 'h28 L.o ]
                         | `_1 of
                             [< `_0 of 'g28 L.z * 'h28 L.o
                              | `_1 of 'g28 L.o * 'h28 L.o ] ] ]
                   as 'f28) *
                  'u28 &
                  'v28 L.z * 'w28 L.z
              | `_1 of
                  'd28 L.o * 'e28 L.o &
                  'f28 * 'u28 ]
             as 'c28) *
            ([< `_0 of
                  'i29 L.z * 'j29 L.z &
                  ([< `_0 of
                        'h7 &
                        [< `_0 of
                             [< `_0 of 'l29 L.z * 'm29 L.z
                              | `_1 of 'l29 L.o * 'm29 L.z ]
                         | `_1 of
                             [< `_0 of 'l29 L.o * 'm29 L.z
                              | `_1 of 'l29 L.z * 'm29 L.o ] ]
                    | `_1 of
                        'h7 &
                        [< `_0 of
                             [< `_0 of 'l29 L.o * 'm29 L.z
                              | `_1 of 'l29 L.z * 'm29 L.o ]
                         | `_1 of
                             [< `_0 of 'l29 L.z * 'm29 L.o
                              | `_1 of 'l29 L.o * 'm29 L.o ] ] ]
                   as 'k29) *
                  'z29 &
                  'a30 L.z * 'b30 L.z
              | `_1 of
                  'i29 L.o * 'j29 L.o &
                  'k29 * 'z29 ]
             as 'h29) *
            ([< `_0 of
                  'n30 L.z * 'o30 L.z &
                  ([< `_0 of
                        'o10 &
                        [< `_0 of
                             [< `_0 of 'q30 L.z * 'r30 L.z
                              | `_1 of 'q30 L.o * 'r30 L.z ]
                         | `_1 of
                             [< `_0 of 'q30 L.o * 'r30 L.z
                              | `_1 of 'q30 L.z * 'r30 L.o ] ]
                    | `_1 of
                        'o10 &
                        [< `_0 of
                             [< `_0 of 'q30 L.o * 'r30 L.z
                              | `_1 of 'q30 L.z * 'r30 L.o ]
                         | `_1 of
                             [< `_0 of 'q30 L.z * 'r30 L.o
                              | `_1 of 'q30 L.o * 'r30 L.o ] ] ]
                   as 'p30) *
                  'e31 &
                  'f31 L.z * 'g31 L.z
              | `_1 of
                  'n30 L.o * 'o30 L.o &
                  'p30 * 'e31 ]
             as 'm30)
        | `_1 of 'w * 'y * 'a1 * 'c1 * 'e1 & 'w26 * 'x26 * 'c28 * 'h29 * 'm30 ];
  overflow : 'r31 L.z;
  s : [< `_0 of
           's31 L.z * 't31 L.z * 'u31 L.z &
           ([< `_0 of
                 'w31 L.z * 'x31 L.z &
                 ([< `_0 of
                       'z31 * 'a32 &
                       ([< `_0 of
                             [< `_0 of
                                  [< `_0 of
                                       [< `_0 of 'd32 L.z | `_1 of 'd32 L.z ]
                                       as 'z2
                                   | `_1 of 'z2 ] &
                                  [< `_0 of
                                       [< `_0 of
                                            [< `_0 of
                                                 [ `_1 of 'h32 ] &
                                                 'i32
                                             | `_1 of
                                                 [ `_0 of 'h32 ] &
                                                 'i32 ]
                                            as 'g32
                                        | `_1 of 'g32 ]
                                       as 'f32
                                   | `_1 of 'f32 ]
                                  as 'e32 &
                                  [< `_0 of
                                       [< `_0 of 'p32 L.z | `_1 of 'p32 L.z ]
                                       as 'z210
                                   | `_1 of 'z210 ]
                              | `_1 of
                                  [< `_0 of
                                       [< `_0 of 'd32 L.o | `_1 of 'd32 L.z ]
                                   | `_1 of
                                       [< `_0 of 'd32 L.z | `_1 of 'd32 L.o ] ] &
                                  'e32 ]
                             as 'c32
                         | `_1 of 'c32 ]
                        as 'b32) *
                       ([< `_0 of
                             'w32 L.z * 'x32 L.z &
                             ([< `_0 of
                                   'x2 &
                                   [< `_0 of
                                        [< `_0 of 'z32 L.z * 'a33 L.z
                                         | `_1 of 'z32 L.o * 'a33 L.z ]
                                    | `_1 of
                                        [< `_0 of 'z32 L.o * 'a33 L.z
                                         | `_1 of 'z32 L.z * 'a33 L.o ] ]
                               | `_1 of
                                   'x2 &
                                   [< `_0 of
                                        [< `_0 of 'z32 L.o * 'a33 L.z
                                         | `_1 of 'z32 L.z * 'a33 L.o ]
                                    | `_1 of
                                        [< `_0 of 'z32 L.z * 'a33 L.o
                                         | `_1 of 'z32 L.o * 'a33 L.o ] ] ]
                              as 'y32) *
                             'n33 &
                             'o33 L.z * 'p33 L.z
                         | `_1 of
                             'w32 L.o * 'x32 L.o &
                             'y32 * 'n33 ]
                        as 'v32)
                   | `_1 of 't2 * 'v2 & 'b32 * 'v32 ]
                  as 'y31) *
                 ([< `_0 of 'n33 & 'f32 | `_1 of 'y2 & 'f32 ] as 'a34) &
                 'b34 L.z * 'c34 L.z
             | `_1 of
                 'w31 L.o * 'x31 L.o &
                 'y31 * 'a34 ]
            as 'v31) *
           ([< `_0 of
                 'p27 * 'u28 * 'z29 * 'e31 &
                 ([< `_0 of
                       'p34 L.z * 'q34 L.z &
                       'r34 *
                       ([< `_0 of
                             't34 L.z * 'u34 L.z * 'v34 L.z &
                             ([< `_0 of
                                   [< `_0 of 'x34 L.o | `_1 of 'x34 L.z ] &
                                   [< `_0 of
                                        [< `_0 of
                                             [< `_0 of
                                                  [< `_0 of 'a35 L.z
                                                   | `_1 of 'a35 L.z ]
                                                  as 'z216
                                              | `_1 of 'z216 ] &
                                             [< `_0 of 'b32 | `_1 of 'b32 ]
                                             as 'b35
                                         | `_1 of
                                             [< `_0 of
                                                  [< `_0 of 'a35 L.o
                                                   | `_1 of 'a35 L.z ]
                                              | `_1 of
                                                  [< `_0 of 'a35 L.z
                                                   | `_1 of 'a35 L.o ] ] &
                                             'b35 ]
                                        as 'z34
                                    | `_1 of 'z34 ]
                                   as 'y34 &
                                   [< `_0 of 'i35 L.o | `_1 of 'i35 L.z ]
                               | `_1 of
                                   [< `_0 of 'x34 L.z | `_1 of 'x34 L.o ] &
                                   'y34 ]
                              as 'w34) *
                             'b35 * 'e32 &
                             'o35 L.z * 'p35 L.z * 'q35 L.z
                         | `_1 of
                             't34 L.o * 'u34 L.o * 'v34 L.o &
                             'w34 * 'b35 * 'e32 ]
                        as 's34) &
                       'g36 L.z * 'h36 L.z
                   | `_1 of
                       'p34 L.o * 'q34 L.o &
                       'r34 * 's34 ]
                  as 'o34) *
                 ([< `_0 of
                       't36 L.z * 'u36 L.z &
                       ([< `_0 of
                             'l2 &
                             [< `_0 of
                                  [< `_0 of 'w36 L.z * 'x36 L.z
                                   | `_1 of 'w36 L.o * 'x36 L.z ]
                              | `_1 of
                                  [< `_0 of 'w36 L.o * 'x36 L.z
                                   | `_1 of 'w36 L.z * 'x36 L.o ] ]
                         | `_1 of
                             'l2 &
                             [< `_0 of
                                  [< `_0 of 'w36 L.o * 'x36 L.z
                                   | `_1 of 'w36 L.z * 'x36 L.o ]
                              | `_1 of
                                  [< `_0 of 'w36 L.z * 'x36 L.o
                                   | `_1 of 'w36 L.o * 'x36 L.o ] ] ]
                        as 'v36) *
                       'k37 &
                       'l37 L.z * 'm37 L.z
                   | `_1 of
                       't36 L.o * 'u36 L.o &
                       'v36 * 'k37 ]
                  as 's36) *
                 ([< `_0 of
                       'y37 L.z * 'z37 L.z &
                       ([< `_0 of
                             'r5 &
                             [< `_0 of
                                  [< `_0 of 'b38 L.z * 'c38 L.z
                                   | `_1 of 'b38 L.o * 'c38 L.z ]
                              | `_1 of
                                  [< `_0 of 'b38 L.o * 'c38 L.z
                                   | `_1 of 'b38 L.z * 'c38 L.o ] ] 
                         | `_1 of
                             'r5 &
                             [< `_0 of
                                  [< `_0 of 'b38 L.o * 'c38 L.z
                                   | `_1 of 'b38 L.z * 'c38 L.o ]
                              | `_1 of
                                  [< `_0 of 'b38 L.z * 'c38 L.o
                                   | `_1 of 'b38 L.o * 'c38 L.o ] ] ]
                        as 'a38) *
                       'p38 &
                       'q38 L.z * 'r38 L.z
                   | `_1 of
                       'y37 L.o * 'z37 L.o &
                       'a38 * 'p38 ]
                  as 'x37) *
                 ([< `_0 of
                       'd39 L.z * 'e39 L.z &
                       ([< `_0 of
                             'i7 &
                             [< `_0 of
                                  [< `_0 of 'g39 L.z * 'h39 L.z
                                   | `_1 of 'g39 L.o * 'h39 L.z ]
                              | `_1 of
                                  [< `_0 of 'g39 L.o * 'h39 L.z
                                   | `_1 of 'g39 L.z * 'h39 L.o ] ] 
                         | `_1 of
                             'i7 &
                             [< `_0 of
                                  [< `_0 of 'g39 L.o * 'h39 L.z
                                   | `_1 of 'g39 L.z * 'h39 L.o ]
                              | `_1 of
                                  [< `_0 of 'g39 L.z * 'h39 L.o
                                   | `_1 of 'g39 L.o * 'h39 L.o ] ] ]
                        as 'f39) *
                       'u39 &
                       'v39 L.z * 'w39 L.z
                   | `_1 of
                       'd39 L.o * 'e39 L.o &
                       'f39 * 'u39 ]
                  as 'c39)
             | `_1 of 'h1 * 'j1 * 'l1 * 'n1 & 'o34 * 's36 * 'x37 * 'c39 ]
            as 'n34) *
           ([< `_0 of
                 'k37 * 'p38 * 'u39 &
                 'y34 *
                 ([< `_0 of
                       'j40 L.z * 'k40 L.z &
                       ([< `_0 of
                             's2 &
                             [< `_0 of
                                  [< `_0 of 'm40 L.z * 'n40 L.z
                                   | `_1 of 'm40 L.o * 'n40 L.z ]
                              | `_1 of
                                  [< `_0 of 'm40 L.o * 'n40 L.z
                                   | `_1 of 'm40 L.z * 'n40 L.o ] ] 
                         | `_1 of
                             's2 &
                             [< `_0 of
                                  [< `_0 of 'm40 L.o * 'n40 L.z
                                   | `_1 of 'm40 L.z * 'n40 L.o ]
                              | `_1 of
                                  [< `_0 of 'm40 L.z * 'n40 L.o
                                   | `_1 of 'm40 L.o * 'n40 L.o ] ]  ]
                        as 'l40) *
                       'z31 &
                       'a41 L.z * 'b41 L.z
                   | `_1 of
                       'j40 L.o * 'k40 L.o &
                       'l40 * 'z31 ]
                  as 'i40) *
                 ([< `_0 of
                       'n41 L.z * 'o41 L.z &
                       ([< `_0 of
                             's5 &
                             [< `_0 of
                                  [< `_0 of 'q41 L.z * 'r41 L.z
                                   | `_1 of 'q41 L.o * 'r41 L.z ]
                              | `_1 of
                                  [< `_0 of 'q41 L.o * 'r41 L.z
                                   | `_1 of 'q41 L.z * 'r41 L.o ] ]
                         | `_1 of
                             's5 &
                             [< `_0 of
                                  [< `_0 of 'q41 L.o * 'r41 L.z
                                   | `_1 of 'q41 L.z * 'r41 L.o ]
                              | `_1 of
                                  [< `_0 of 'q41 L.z * 'r41 L.o
                                   | `_1 of 'q41 L.o * 'r41 L.o ] ] ]
                        as 'p41) *
                       'a32 &
                       'e42 L.z * 'f42 L.z
                   | `_1 of
                       'n41 L.o * 'o41 L.o &
                       'p41 * 'a32]
                  as 'm41)
             | `_1 of 'm2 * 'o2 * 'q2 & 'y34 * 'i40 * 'm41 ]
            as 'h40) &
           'q42 L.z * 'r42 L.z * 's42 L.z
       | `_1 of
           's31 L.o * 't31 L.o * 'u31 L.o &
           'v31 * 'n34 * 'h40 ] >
      t
  -> < b0 : 'r13; b1 : 'w20; b2 : 'w26; overflow : 'i32; s : 'r34 > t =
                                                             fun x y -> Natural.(create @@ to_int x * to_int y )



module Ops = struct
  let ( + ) x y = add x y
  let ( - ) x y = minus x y
  let ( ~- ) x = uminus x
  let ( * ) k l = mult k l
end
