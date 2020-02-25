open GT
open OCanren
open Std
open Nat

let fuluMaxLen x0 x1 x2 =
  let rec maxLengtho y0 y1 y2 =
    fresh (x6 x5 x4) (y0 === nil () &&& (y2 === zero) &&& (y1 === zero) ||| (y0 === x4 % x5 &&& (y2 === succ x6) &&& maxo1Lengtho x4 x5 y1 x6))
  and maxo1Lengtho y3 y4 y5 y6 =
    fresh (x66 x65 x64 x55 x44 x24 x23 x22)
      ( y4 === nil () &&& (y6 === zero)
      &&& (y3 === zero &&& (y5 === zero))
      ||| ( y4 === x22 % x23
          &&& (y6 === succ x24)
          &&& (y3 === zero &&& maxo1Lengtho x22 x23 y5 x24)
          ||| ( y4 === nil () &&& (y6 === zero)
              &&& (y3 === succ x44 &&& (y5 === y3))
              ||| ( y4 === x22 % x23
                  &&& (y6 === succ x24)
                  &&& ( y3 === succ x55
                      &&& (x23 === nil ())
                      &&& (x24 === zero) &&& leoMaxo1 x22 x55 y5
                      ||| ( y3 === succ x55
                          &&& (x23 === x64 % x65)
                          &&& (x24 === succ x66)
                          &&& leoMaxo1Lengtho x22 x55 x64 x65 y5 x66
                          ||| ( y3 === succ x55
                              &&& (x23 === nil ())
                              &&& (x24 === zero) &&& gtoMaxo1 x22 x55 y5
                              ||| (y3 === succ x55 &&& (x23 === x64 % x65) &&& (x24 === succ x66) &&& gtoMaxo1Lengtho x22 x55 x64 x65 y5 x66) ) ) ) ) ) ) )
  and leoMaxo1 y7 y8 y9 = fresh (x69) (y7 === zero &&& (y9 === succ y8) ||| (y7 === succ x69 &&& (y9 === succ y8) &&& leo x69 y8))
  and leo y10 y11 = fresh (x81 x80) (y10 === zero ||| (y10 === succ x80 &&& (y11 === succ x81) &&& leo x80 x81))
  and leoMaxo1Lengtho y12 y13 y14 y15 y16 y17 =
    fresh
      (x366 x368 x367 x364 x362 x363 x360 x336 x333 x332 x338 x335 x321 x327 x326 x323 x325 x293 x290 x289 x295 x292 x270 x269 x282 x281 x280 x272 x247 x246
         x249 x241 x240 x237 x210 x209 x212 x86 x96 x95 x94)
      ( y12 === zero
      &&& (y15 === nil ())
      &&& (y17 === zero) &&& leoMaxo1 y14 y13 y16
      ||| ( y12 === zero
          &&& (y15 === x94 % x95)
          &&& (y17 === succ x96)
          &&& leoMaxo1Lengtho y14 y13 x94 x95 y16 x96
          ||| ( y12 === zero
              &&& (y15 === nil ())
              &&& (y17 === zero) &&& gtoMaxo1 y14 y13 y16
              ||| ( y12 === zero
                  &&& (y15 === x94 % x95)
                  &&& (y17 === succ x96)
                  &&& gtoMaxo1Lengtho y14 y13 x94 x95 y16 x96
                  ||| ( y12 === succ x86
                      &&& (y15 === nil ())
                      &&& (y17 === zero)
                      &&& ( x86 === zero &&& (y14 === zero)
                          &&& (y16 === succ y13)
                          ||| ( x86 === zero
                              &&& (y14 === succ x212)
                              &&& (y16 === succ y13)
                              &&& leo x212 y13
                              ||| ( x86 === succ x209
                                  &&& (y13 === succ x210)
                                  &&& (y14 === zero)
                                  &&& (y16 === succ y13)
                                  &&& leo x209 x210
                                  ||| (x86 === succ x209 &&& (y13 === succ x210) &&& (y14 === succ x212) &&& (y16 === succ y13) &&& leoLeo x209 x210 x212) ) )
                          )
                      ||| ( y12 === succ x86
                          &&& (y15 === x237 % x240)
                          &&& (y17 === succ x241)
                          &&& (leoMaxo1Lengtho y14 y13 x237 x240 y16 x241 &&& leo x86 y13)
                          ||| ( y12 === succ x86
                              &&& (y15 === nil ())
                              &&& (y17 === zero)
                              &&& ( x86 === zero
                                  &&& (y14 === succ x249)
                                  &&& (y16 === y14) &&& gto x249 y13
                                  ||| (x86 === succ x246 &&& (y13 === succ x247) &&& (y14 === succ x249) &&& (y16 === y14) &&& leoGto x246 x247 x249) )
                              ||| ( y12 === succ x86
                                  &&& (y15 === x94 % x95)
                                  &&& (y17 === succ x96)
                                  &&& ( x86 === zero
                                      &&& (y14 === succ x272)
                                      &&& (x95 === nil ())
                                      &&& (x96 === zero) &&& gtoLeoMaxo1 x272 y13 x94 y16
                                      ||| ( x86 === zero
                                          &&& (y14 === succ x272)
                                          &&& (x95 === x280 % x281)
                                          &&& (x96 === succ x282)
                                          &&& gtoLeoMaxo1Lengtho x272 y13 x94 x280 x281 y16 x282
                                          ||| ( x86 === zero
                                              &&& (y14 === succ x272)
                                              &&& (x95 === nil ())
                                              &&& (x96 === zero) &&& gtoGtoMaxo1 x272 y13 x94 y16
                                              ||| ( x86 === zero
                                                  &&& (y14 === succ x272)
                                                  &&& (x95 === x280 % x281)
                                                  &&& (x96 === succ x282)
                                                  &&& gtoGtoMaxo1Lengtho x272 y13 x94 x280 x281 y16 x282
                                                  ||| ( x86 === succ x269
                                                      &&& (y13 === succ x270)
                                                      &&& (y14 === succ x272)
                                                      &&& (x95 === nil ())
                                                      &&& (x96 === zero)
                                                      &&& ( x269 === zero
                                                          &&& (x272 === succ x292)
                                                          &&& (x94 === zero)
                                                          &&& (y16 === succ x272)
                                                          &&& gto x292 x270
                                                          ||| ( x269 === zero
                                                              &&& (x272 === succ x292)
                                                              &&& (x94 === succ x295)
                                                              &&& (y16 === succ x272)
                                                              &&& gtoLeo x292 x270 x295
                                                              ||| ( x269 === succ x289
                                                                  &&& (x270 === succ x290)
                                                                  &&& (x272 === succ x292)
                                                                  &&& (x293 === x270) &&& (x94 === zero)
                                                                  &&& (y16 === succ x272)
                                                                  &&& leoGto x289 x290 x292
                                                                  ||| ( x269 === succ x289
                                                                      &&& (x270 === succ x290)
                                                                      &&& (x272 === succ x292)
                                                                      &&& (x293 === x270)
                                                                      &&& (x94 === succ x295)
                                                                      &&& (y16 === succ x272)
                                                                      &&& leoGtoLeo x289 x290 x292 x295 ) ) ) )
                                                      ||| ( x86 === succ x269
                                                          &&& (y13 === succ x270)
                                                          &&& (y14 === succ x325)
                                                          &&& (x95 === x323 % x326)
                                                          &&& (x96 === succ x327)
                                                          &&& (x321 === x94 &&& leoMaxo1Lengtho x321 x325 x323 x326 y16 x327 &&& leoGto x269 x270 x325)
                                                          ||| ( x86 === succ x269
                                                              &&& (y13 === succ x270)
                                                              &&& (y14 === succ x272)
                                                              &&& (x95 === nil ())
                                                              &&& (x96 === zero)
                                                              &&& ( x269 === zero
                                                                  &&& (x272 === succ x335)
                                                                  &&& (x94 === succ x338)
                                                                  &&& (y16 === x94) &&& gtoGto x335 x270 x338
                                                                  ||| ( x269 === succ x332
                                                                      &&& (x270 === succ x333)
                                                                      &&& (x272 === succ x335)
                                                                      &&& (x336 === x270)
                                                                      &&& (x94 === succ x338)
                                                                      &&& (y16 === x94) &&& leoGtoGto x332 x333 x335 x338 ) )
                                                              ||| ( x86 === succ x360
                                                                  &&& (y13 === succ x363)
                                                                  &&& (y14 === succ x362)
                                                                  &&& (x95 === x364 % x367)
                                                                  &&& (x96 === succ x368)
                                                                  &&& ( x366 === x94 &&& leoGto x360 x363 x362
                                                                      &&& (x366 === x94 &&& _maxo1Lengtho x364 x367 x366 y16 x368 &&& _gto x94 x362) ) ) ) ) )
                                                  ) ) ) ) ) ) ) ) ) ) ) )
  and gtoMaxo1 y18 y19 y20 = fresh (x101) (y18 === succ x101 &&& (y20 === y18) &&& gto x101 y19)
  and gto y21 y22 = fresh (x112 x111 x110) (y21 === succ x110 &&& (y22 === zero) ||| (y21 === succ x111 &&& (y22 === succ x112) &&& gto x111 x112))
  and gtoMaxo1Lengtho y23 y24 y25 y26 y27 y28 =
    fresh (x127 x126 x125 x117)
      ( y23 === succ x117
      &&& (y26 === nil ())
      &&& (y28 === zero) &&& gtoLeoMaxo1 x117 y24 y25 y27
      ||| ( y23 === succ x117
          &&& (y26 === x125 % x126)
          &&& (y28 === succ x127)
          &&& gtoLeoMaxo1Lengtho x117 y24 y25 x125 x126 y27 x127
          ||| ( y23 === succ x117
              &&& (y26 === nil ())
              &&& (y28 === zero) &&& gtoGtoMaxo1 x117 y24 y25 y27
              ||| (y23 === succ x117 &&& (y26 === x125 % x126) &&& (y28 === succ x127) &&& gtoGtoMaxo1Lengtho x117 y24 y25 x125 x126 y27 x127) ) ) )
  and gtoLeoMaxo1 y29 y30 y31 y32 =
    fresh (x131 x130 x133 x129)
      ( y29 === succ x129 &&& (y30 === zero) &&& (y31 === zero)
      &&& (y32 === succ y29)
      ||| ( y29 === succ x129 &&& (y30 === zero)
          &&& (y31 === succ x133)
          &&& (y32 === succ y29)
          &&& _leo x133 x129
          ||| ( y29 === succ x130
              &&& (y30 === succ x131)
              &&& (y31 === zero)
              &&& (y32 === succ y29)
              &&& gto x130 x131
              ||| (y29 === succ x130 &&& (y30 === succ x131) &&& (y31 === succ x133) &&& (y32 === succ y29) &&& gtoLeo x130 x131 x133) ) ) )
  and _leo y33 y34 = fresh (x144) (y33 === zero ||| (y33 === succ x144 &&& leo x144 y34))
  and gtoLeo y35 y36 y37 =
    fresh (x152 x151 x154 x150)
      ( y35 === succ x150 &&& (y36 === zero) &&& (y37 === zero)
      ||| ( y35 === succ x150 &&& (y36 === zero)
          &&& (y37 === succ x154)
          &&& _leo x154 x150
          ||| ( y35 === succ x151
              &&& (y36 === succ x152)
              &&& (y37 === zero) &&& gto x151 x152
              ||| (y35 === succ x151 &&& (y36 === succ x152) &&& (y37 === succ x154) &&& gtoLeo x151 x152 x154) ) ) )
  and gtoLeoMaxo1Lengtho y38 y39 y40 y41 y42 y43 y44 = leoMaxo1Lengtho y40 y38 y41 y42 y43 y44 &&& gto y38 y39
  and gtoGtoMaxo1 y45 y46 y47 y48 =
    fresh (x173 x172 x175 x171)
      ( y45 === succ x171 &&& (y46 === zero)
      &&& (y47 === succ x175)
      &&& (y48 === y47) &&& _gto x175 x171
      ||| (y45 === succ x172 &&& (y46 === succ x173) &&& (y47 === succ x175) &&& (y48 === y47) &&& gtoGto x172 x173 x175) )
  and _gto y49 y50 = fresh (x185) (y49 === succ x185 &&& gto x185 y50)
  and gtoGto y51 y52 y53 =
    fresh (x191 x190 x193 x189)
      ( y51 === succ x189 &&& (y52 === zero)
      &&& (y53 === succ x193)
      &&& _gto x193 x189
      ||| (y51 === succ x190 &&& (y52 === succ x191) &&& (y53 === succ x193) &&& gtoGto x190 x191 x193) )
  and gtoGtoMaxo1Lengtho y54 y55 y56 y57 y58 y59 y60 = gtoMaxo1Lengtho y56 y54 y57 y58 y59 y60 &&& gto y54 y55
  and leoLeo y61 y62 y63 =
    fresh (x226 x225 x228)
      ( y61 === zero &&& (y63 === zero)
      ||| ( y61 === zero
          &&& (y63 === succ x228)
          &&& leo x228 y62
          ||| ( y61 === succ x225
              &&& (y62 === succ x226)
              &&& (y63 === zero) &&& leo x225 x226
              ||| (y61 === succ x225 &&& (y62 === succ x226) &&& (y63 === succ x228) &&& leoLeo x225 x226 x228) ) ) )
  and leoGto y64 y65 y66 =
    fresh (x261 x260 x263)
      (y64 === zero &&& (y66 === succ x263) &&& gto x263 y65 ||| (y64 === succ x260 &&& (y65 === succ x261) &&& (y66 === succ x263) &&& leoGto x260 x261 x263))
  and leoGtoLeo y67 y68 y69 y70 =
    fresh (x309 x308 x314 x311)
      ( y67 === zero
      &&& (y69 === succ x311)
      &&& (y70 === zero) &&& gto x311 y68
      ||| ( y67 === zero
          &&& (y69 === succ x311)
          &&& (y70 === succ x314)
          &&& gtoLeo x311 y68 x314
          ||| ( y67 === succ x308
              &&& (y68 === succ x309)
              &&& (y69 === succ x311)
              &&& (y70 === zero) &&& leoGto x308 x309 x311
              ||| (y67 === succ x308 &&& (y68 === succ x309) &&& (y69 === succ x311) &&& (y70 === succ x314) &&& leoGtoLeo x308 x309 x311 x314) ) ) )
  and leoGtoGto y71 y72 y73 y74 =
    fresh (x350 x349 x355 x352)
      ( y71 === zero
      &&& (y73 === succ x352)
      &&& (y74 === succ x355)
      &&& gtoGto x352 y72 x355
      ||| (y71 === succ x349 &&& (y72 === succ x350) &&& (y73 === succ x352) &&& (y74 === succ x355) &&& leoGtoGto x349 x350 x352 x355) )
  and _maxo1Lengtho y75 y76 y77 y78 y79 =
    fresh
      (x425 x424 x421 x411 x410 x409 x405 x404 x402 x392 x391)
      ( y76 === nil () &&& (y79 === zero)
      &&& (y75 === zero &&& (y78 === y77) ||| (y75 === succ x391 &&& (y77 === succ x392) &&& (y78 === y77) &&& leo x391 x392))
      ||| ( y76 === x402 % x404
          &&& (y79 === succ x405)
          &&& (_maxo1Lengtho x402 x404 y77 y78 x405 &&& leo y75 y77)
          ||| ( y76 === nil () &&& (y79 === zero)
              &&& (y75 === succ x409 &&& (y77 === zero) &&& (y78 === y75) ||| (y75 === succ x410 &&& (y77 === succ x411) &&& (y78 === y75) &&& gto x410 x411))
              ||| (y76 === x421 % x424 &&& (y79 === succ x425) &&& (_maxo1Lengtho x421 x424 y75 y78 x425 &&& gto y75 y77)) ) ) )
  in
  maxLengtho x0 x1 x2
