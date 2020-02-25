open GT
open OCanren
open Std
open Nat

open LogicExpr

let recuLogint x0 x1 =
  let rec loginto y0 y1 =
    fresh
      (x480 x478 x477 x479 x475 x622 x621 x563 x562 x615 x612 x616 x613 x614 x611 x604 x601 x605 x602 x603 x600 x570 x566 x567 x564 x476 x555 x554 x528 x547
         x526 x546 x541 x540 x524 x516 x515 x487 x508 x485 x507 x502 x501 x483 x216 x214 x213 x215 x211 x434 x433 x295 x294 x427 x424 x428 x425 x426 x423 x332
         x329 x333 x330 x331 x328 x302 x298 x299 x296 x212 x287 x286 x262 x279 x260 x278 x273 x272 x258 x250 x249 x223 x242 x221 x241 x236 x235 x8 x219 x6 x5
         x204 x203 x22 x90 x20 x89 x35 x34 x7 x18 x3 x4)
      ( y1 === ltrue ()
      ||| ( y1 === var x4 &&& lookupo y0 x4
          ||| ( y1 === neg x3
              &&& ( x3 === lfalse ()
                  ||| ( x3 === var x18 &&& lookupoNoto y0 x18 x7
                      ||| ( x3 === neg x34
                          &&& (_loginto y0 x34 x35 &&& (noto x7 &&& _noto x35 x7))
                          ||| ( x3 === conj x89 x20
                              &&& (_loginto y0 x89 x90 &&& (noto x7 &&& logintoAndo y0 x20 x22 x90 x7))
                              ||| (x3 === disj x203 x20 &&& (_loginto y0 x203 x204 &&& (noto x7 &&& logintoOro y0 x20 x22 x204 x7))) ) ) ) )
              ||| ( y1 === conj x5 x6
                  &&& ( x5 === ltrue ()
                      &&& ( x6 === ltrue ()
                          ||| ( x6 === var x219 &&& _lookupoAndo y0 x219 x8
                              ||| ( x6 === neg x235
                                  &&& (_loginto y0 x235 x236 &&& (_ando x8 &&& _noto x236 x8))
                                  ||| ( x6 === conj x241 x221
                                      &&& (_loginto y0 x241 x242 &&& (_ando x8 &&& logintoAndo y0 x221 x223 x242 x8))
                                      ||| (x6 === disj x249 x221 &&& (_loginto y0 x249 x250 &&& (_ando x8 &&& logintoOro y0 x221 x223 x250 x8))) ) ) ) )
                      ||| ( x5 === lfalse ()
                          &&& ( x6 === var x258 &&& __lookupoAndo y0 x258 x8
                              ||| ( x6 === neg x272
                                  &&& (_loginto y0 x272 x273 &&& _noto x273 x8)
                                  ||| ( x6 === conj x278 x260
                                      &&& (_loginto y0 x278 x279 &&& logintoAndo y0 x260 x262 x279 x8)
                                      ||| (x6 === disj x286 x260 &&& (_loginto y0 x286 x287 &&& logintoOro y0 x260 x262 x287 x8)) ) ) )
                          ||| ( x5 === var x212
                              &&& ( y0
                                  === pair x212 x7 % x296
                                  &&& ( x6 === ltrue () &&& (x7 === !!true)
                                      ||| ( x6 === var x299
                                          &&& (x299 === x212 &&& (x8 === x7) &&& (x7 === !!true) ||| ___lookupoAndo x296 x299 x8 x7)
                                          ||| ( x6 === neg x298 &&& _noto x302 x8
                                              ||| ( x6 === conj x328 x331
                                                  &&& ( x330
                                                      === pair x212 x7 % x296
                                                      &&& (x333 === x7) &&& logintoLoginto x330 x328 x329 x331 x332
                                                      &&& (x330 === pair x212 x7 % x296 &&& (x333 === x7) &&& __ando x333 x8 &&& ando x329 x332 x8) )
                                                  ||| ( x6 === disj x423 x426
                                                      &&& ( x425
                                                          === pair x212 x7 % x296
                                                          &&& (x428 === x7) &&& logintoLoginto x425 x423 x424 x426 x427
                                                          &&& (x425 === pair x212 x7 % x296 &&& (x428 === x7) &&& __ando x428 x8 &&& oro x424 x427 x8) ) ) ) )
                                          ) )
                                  ||| ( y0
                                      === pair x294 x295 % x433
                                      &&& ( x434
                                          === pair x294 x295 % x433
                                          &&& ____lookupoAndo x433 x212 x7 x8
                                          &&& (x434 === pair x294 x295 % x433 &&& _loginto x434 x6 x8) ) ) )
                              ||| ( x5 === neg x211 &&& _noto x215 x7
                                  ||| ( x5 === conj x213 x214
                                      &&& (ando x215 x216 x7 &&& _loginto y0 x6 x8)
                                      ||| (x5 === disj x213 x214 &&& (oro x215 x216 x7 &&& _loginto y0 x6 x8)) ) ) ) ) )
                  ||| ( y1 === disj x5 x6
                      &&& ( x5 === ltrue ()
                          &&& ( x6 === ltrue ()
                              ||| ( x6 === lfalse ()
                                  ||| ( x6 === var x483 &&& _lookupoOro y0 x483 x8
                                      ||| ( x6 === neg x501
                                          &&& (_loginto y0 x501 x502 &&& (_oro x8 &&& _noto x502 x8))
                                          ||| ( x6 === conj x507 x485
                                              &&& (_loginto y0 x507 x508 &&& (_oro x8 &&& logintoAndo y0 x485 x487 x508 x8))
                                              ||| (x6 === disj x515 x485 &&& (_loginto y0 x515 x516 &&& (_oro x8 &&& logintoOro y0 x485 x487 x516 x8))) ) ) )
                                  ) )
                          ||| ( x5 === lfalse ()
                              &&& ( x6 === ltrue ()
                                  ||| ( x6 === var x524 &&& __lookupoOro y0 x524 x8
                                      ||| ( x6 === neg x540
                                          &&& (_loginto y0 x540 x541 &&& (__oro x8 &&& _noto x541 x8))
                                          ||| ( x6 === conj x546 x526
                                              &&& (_loginto y0 x546 x547 &&& (__oro x8 &&& logintoAndo y0 x526 x528 x547 x8))
                                              ||| (x6 === disj x554 x526 &&& (_loginto y0 x554 x555 &&& (__oro x8 &&& logintoOro y0 x526 x528 x555 x8))) ) ) )
                                  )
                              ||| ( x5 === var x476
                                  &&& ( y0
                                      === pair x476 x7 % x564
                                      &&& ( x6 === ltrue ()
                                          &&& (x7 === !!false ||| (x7 === !!true))
                                          ||| ( x6 === lfalse () &&& (x7 === !!true)
                                              ||| ( x6 === var x567
                                                  &&& (x567 === x476 &&& (x8 === x7) &&& (x7 === !!true) ||| ___lookupoOro x564 x567 x8 x7)
                                                  ||| ( x6 === neg x566 &&& _noto x570 x8
                                                      ||| ( x6 === conj x600 x603
                                                          &&& ( x602
                                                              === pair x476 x7 % x564
                                                              &&& (x605 === x7) &&& logintoLoginto x602 x600 x601 x603 x604
                                                              &&& (x602 === pair x476 x7 % x564 &&& (x605 === x7) &&& ___oro x605 x8 &&& ando x601 x604 x8) )
                                                          ||| ( x6 === disj x611 x614
                                                              &&& ( x613
                                                                  === pair x476 x7 % x564
                                                                  &&& (x616 === x7) &&& logintoLoginto x613 x611 x612 x614 x615
                                                                  &&& (x613 === pair x476 x7 % x564 &&& (x616 === x7) &&& ___oro x616 x8 &&& oro x612 x615 x8)
                                                                  ) ) ) ) ) ) )
                                      ||| ( y0
                                          === pair x562 x563 % x621
                                          &&& ( x622
                                              === pair x562 x563 % x621
                                              &&& ____lookupoOro x621 x476 x7 x8
                                              &&& (x622 === pair x562 x563 % x621 &&& _loginto x622 x6 x8) ) ) )
                                  ||| ( x5 === neg x475 &&& _noto x479 x7
                                      ||| ( x5 === conj x477 x478
                                          &&& (ando x479 x480 x7 &&& _loginto y0 x6 x8)
                                          ||| (x5 === disj x477 x478 &&& (oro x479 x480 x7 &&& _loginto y0 x6 x8)) ) ) ) ) ) ) ) ) ) )
  and lookupo y2 y3 = fresh (x12 x11 x13) (y2 === pair y3 !!true % x13 ||| (y2 === pair x11 x12 % x13 &&& lookupo x13 y3))
  and lookupoNoto y4 y5 y6 = fresh (x28 x27 x29) (y4 === pair y5 y6 % x29 &&& noto y6 ||| (y4 === pair x27 x28 % x29 &&& lookupoNoto x29 y5 y6))
  and noto y7 = y7 === !!false
  and _loginto y8 y9 y10 =
    fresh (x78 x74 x77 x73 x64 x60 x63 x59 x53 x52 x38)
      ( y9 === ltrue () &&& (y10 === !!true)
      ||| ( y9 === lfalse () &&& (y10 === !!false)
          ||| ( y9 === var x38 &&& _lookupo y8 x38 y10
              ||| ( y9 === neg x52
                  &&& (_loginto y8 x52 x53 &&& _noto x53 y10)
                  ||| ( y9 === conj x59 x63
                      &&& (_loginto y8 x59 x60 &&& (_loginto y8 x63 x64 &&& ando x60 x64 y10))
                      ||| (y9 === disj x73 x77 &&& (_loginto y8 x73 x74 &&& (_loginto y8 x77 x78 &&& oro x74 x78 y10))) ) ) ) ) )
  and _lookupo y11 y12 y13 = fresh (x47 x46 x48) (y11 === pair y12 y13 % x48 ||| (y11 === pair x46 x47 % x48 &&& _lookupo x48 y12 y13))
  and _noto y14 y15 = y14 === !!true &&& (y15 === !!false) ||| (y14 === !!false &&& (y15 === !!true))
  and ando y16 y17 y18 =
    y16 === !!false &&& (y17 === !!false) &&& (y18 === !!false)
    ||| ( y16 === !!false &&& (y17 === !!true) &&& (y18 === !!false)
        ||| (y16 === !!true &&& (y17 === !!false) &&& (y18 === !!false) ||| (y16 === !!true &&& (y17 === !!true) &&& (y18 === !!true))) )
  and oro y19 y20 y21 =
    y19 === !!false &&& (y20 === !!false) &&& (y21 === !!false)
    ||| ( y19 === !!false &&& (y20 === !!true) &&& (y21 === !!true)
        ||| (y19 === !!true &&& (y20 === !!false) &&& (y21 === !!true) ||| (y19 === !!true &&& (y20 === !!true) &&& (y21 === !!true))) )
  and logintoAndo y22 y23 y24 y25 y26 =
    fresh (x101 x140 x99 x139 x130 x131 x128 x98 x116 x115 x97)
      ( y23 === ltrue () &&& (y24 === !!true)
      &&& (y25 === !!false &&& (y26 === !!false) ||| (y25 === !!true &&& (y26 === !!true)))
      ||| ( y23 === lfalse () &&& (y24 === !!false)
          &&& (y25 === !!false &&& (y26 === !!false) ||| (y25 === !!true &&& (y26 === !!false)))
          ||| ( y23 === var x97 &&& lookupoAndo y22 x97 y24 y25 y26
              ||| ( y23 === neg x115
                  &&& (_loginto y22 x115 x116 &&& (ando y25 y24 y26 &&& _noto x116 y24))
                  ||| ( y23 === conj x98 x128
                      &&& (logintoAndo y22 x128 x131 x130 y24 &&& (_loginto y22 x128 x131 &&& ando y25 y24 y26))
                      ||| (y23 === disj x139 x99 &&& (_loginto y22 x139 x140 &&& (ando y25 y24 y26 &&& logintoOro y22 x99 x101 x140 y24))) ) ) ) ) )
  and lookupoAndo y27 y28 y29 y30 y31 =
    fresh (x110 x109 x111) (y27 === pair y28 y29 % x111 &&& ando y30 y29 y31 ||| (y27 === pair x109 x110 % x111 &&& lookupoAndo x111 y28 y29 y30 y31))
  and logintoOro y32 y33 y34 y35 y36 =
    fresh (x194 x195 x192 x178 x179 x176 x148 x166 x165 x147)
      ( y33 === ltrue () &&& (y34 === !!true)
      &&& (y35 === !!false &&& (y36 === !!true) ||| (y35 === !!true &&& (y36 === !!true)))
      ||| ( y33 === lfalse () &&& (y34 === !!false)
          &&& (y35 === !!false &&& (y36 === !!false) ||| (y35 === !!true &&& (y36 === !!true)))
          ||| ( y33 === var x147 &&& lookupoOro y32 x147 y34 y35 y36
              ||| ( y33 === neg x165
                  &&& (_loginto y32 x165 x166 &&& (oro y35 y34 y36 &&& _noto x166 y34))
                  ||| ( y33 === conj x148 x176
                      &&& (logintoAndo y32 x176 x179 x178 y34 &&& (_loginto y32 x176 x179 &&& oro y35 y34 y36))
                      ||| (y33 === disj x148 x192 &&& (logintoOro y32 x192 x195 x194 y34 &&& (_loginto y32 x192 x195 &&& oro y35 y34 y36))) ) ) ) ) )
  and lookupoOro y37 y38 y39 y40 y41 =
    fresh (x160 x159 x161) (y37 === pair y38 y39 % x161 &&& oro y40 y39 y41 ||| (y37 === pair x159 x160 % x161 &&& lookupoOro x161 y38 y39 y40 y41))
  and _lookupoAndo y42 y43 y44 =
    fresh (x229 x228 x230) (y42 === pair y43 y44 % x230 &&& _ando y44 ||| (y42 === pair x228 x229 % x230 &&& _lookupoAndo x230 y43 y44))
  and _ando y45 = y45 === !!true
  and __lookupoAndo y46 y47 y48 = fresh (x268 x267 x266) (y46 === pair x266 x267 % x268 &&& __lookupoAndo x268 y47 y48)
  and ___lookupoAndo y49 y50 y51 y52 =
    fresh (x315 x314 x316) (y49 === pair y50 y51 % x316 &&& __ando y52 y51 ||| (y49 === pair x314 x315 % x316 &&& ___lookupoAndo x316 y50 y51 y52))
  and __ando y53 y54 = y53 === !!true &&& (y54 === !!true)
  and logintoLoginto y55 y56 y57 y58 y59 =
    fresh
      (x411 x409 x410 x408 x399 x397 x398 x396 x392 x391 x387 x386 x345 x344 x346 x336)
      ( y56 === ltrue () &&& (y57 === !!true) &&& _loginto y55 y58 y59
      ||| ( y56 === lfalse () &&& (y57 === !!false) &&& _loginto y55 y58 y59
          ||| ( y56 === var x336
              &&& ( y55
                  === pair x336 y57 % x346
                  &&& __loginto x336 y57 x346 y58 y59
                  ||| ( y55
                      === pair x344 x345 % x386
                      &&& (x387 === pair x344 x345 % x386 &&& _lookupo x386 x336 y57 &&& (x387 === pair x344 x345 % x386 &&& _loginto x387 y58 y59)) ) )
              ||| ( y56 === neg x391
                  &&& (logintoLoginto y55 x391 x392 y58 y59 &&& _noto x392 y57)
                  ||| ( y56 === conj x396 x398
                      &&& (logintoLoginto y55 x396 x397 x398 x399 &&& (ando x397 x399 y57 &&& _loginto y55 y58 y59))
                      ||| (y56 === disj x408 x410 &&& (logintoLoginto y55 x408 x409 x410 x411 &&& (oro x409 x411 y57 &&& _loginto y55 y58 y59))) ) ) ) ) )
  and __loginto y60 y61 y62 y63 y64 =
    fresh
      (x382 x379 x380 x381 x378 x373 x370 x371 x372 x369 x364 x363 x349)
      ( y63 === ltrue () &&& (y64 === !!true)
      ||| ( y63 === lfalse () &&& (y64 === !!false)
          ||| ( y63 === var x349
              &&& (x349 === y60 &&& (y64 === y61) ||| _lookupo y62 x349 y64)
              ||| ( y63 === neg x363
                  &&& (__loginto y60 y61 y62 x363 x364 &&& _noto x364 y64)
                  ||| ( y63 === conj x369 x372
                      &&& (x371 === pair y60 y61 % y62 &&& logintoLoginto x371 x369 x370 x372 x373 &&& ando x370 x373 y64)
                      ||| (y63 === disj x378 x381 &&& (x380 === pair y60 y61 % y62 &&& logintoLoginto x380 x378 x379 x381 x382 &&& oro x379 x382 y64)) ) ) ) )
      )
  and ____lookupoAndo y65 y66 y67 y68 =
    fresh (x437 x436 x438) (y65 === pair y66 y67 % x438 &&& __ando y67 y68 ||| (y65 === pair x436 x437 % x438 &&& ____lookupoAndo x438 y66 y67 y68))
  and _lookupoOro y69 y70 y71 =
    fresh (x494 x493 x495) (y69 === pair y70 y71 % x495 &&& _oro y71 ||| (y69 === pair x493 x494 % x495 &&& _lookupoOro x495 y70 y71))
  and _oro y72 = y72 === !!false ||| (y72 === !!true)
  and __lookupoOro y73 y74 y75 =
    fresh (x534 x533 x535) (y73 === pair y74 y75 % x535 &&& __oro y75 ||| (y73 === pair x533 x534 % x535 &&& __lookupoOro x535 y74 y75))
  and __oro y76 = y76 === !!true
  and ___lookupoOro y77 y78 y79 y80 =
    fresh (x585 x584 x586) (y77 === pair y78 y79 % x586 &&& ___oro y80 y79 ||| (y77 === pair x584 x585 % x586 &&& ___lookupoOro x586 y78 y79 y80))
  and ___oro y81 y82 = y81 === !!false &&& (y82 === !!true) ||| (y81 === !!true &&& (y82 === !!false) ||| (y81 === !!true &&& (y82 === !!true)))
  and ____lookupoOro y83 y84 y85 y86 =
    fresh (x625 x624 x626) (y83 === pair y84 y85 % x626 &&& ___oro y85 y86 ||| (y83 === pair x624 x625 % x626 &&& ____lookupoOro x626 y84 y85 y86))
  in
  loginto x0 x1
