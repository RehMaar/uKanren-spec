open GT
open OCanren
open Std
open Nat

open LogicExpr

let sequLogint x0 x1 =
  let rec loginto y0 y1 =
    fresh
      (x400 x398 x397 x399 x395 x723 x721 x722 x720 x711 x709 x710 x708 x680 x676 x677 x396 x215 x213 x212 x214 x210 x357 x355 x356 x354 x265 x263 x264 x262 x8
         x224 x220 x221 x211 x6 x5 x203 x202 x22 x91 x20 x90 x7 x35 x34 x18 x3 x4)
      ( y1 === ltrue ()
      ||| ( y1 === var x4 &&& lookupo y0 x4
          ||| ( y1 === neg x3
              &&& ( x3 === lfalse ()
                  ||| ( x3 === var x18 &&& _lookupo y0 x18
                      ||| ( x3 === neg x34
                          &&& (_loginto y0 x34 x35 &&& (_noto x7 &&& noto x35 x7))
                          ||| ( x3 === conj x90 x20
                              &&& (_loginto y0 x90 x91 &&& (_noto x7 &&& logintoAndo y0 x20 x22 x91 x7))
                              ||| (x3 === disj x202 x20 &&& (_loginto y0 x202 x203 &&& (_noto x7 &&& logintoOro y0 x20 x22 x203 x7))) ) ) ) )
              ||| ( y1 === conj x5 x6
                  &&& ( x5 === ltrue () &&& loginto y0 x6
                      ||| ( x5 === var x211
                          &&& ( x6 === ltrue () &&& lookupoAndo y0 x211 x7
                              ||| ( x6 === lfalse () &&& _lookupoAndo y0 x211 x7
                                  ||| ( x6 === var x221 &&& lookupoLookupo y0 x211 x221
                                      ||| ( x6 === neg x220 &&& noto x224 x8
                                          ||| ( x6 === conj x262 x264
                                              &&& (logintoLoginto y0 x262 x263 x264 x265 &&& (_ando x7 x8 &&& (__lookupo y0 x211 x7 &&& ando x263 x265 x8)))
                                              ||| ( x6 === disj x354 x356
                                                  &&& (logintoLoginto y0 x354 x355 x356 x357 &&& (_ando x7 x8 &&& (__lookupo y0 x211 x7 &&& oro x355 x357 x8)))
                                                  ) ) ) ) ) )
                          ||| ( x5 === neg x210 &&& noto x214 x7
                              ||| ( x5 === conj x212 x213
                                  &&& (ando x214 x215 x7 &&& _loginto y0 x6 x8)
                                  ||| (x5 === disj x212 x213 &&& (oro x214 x215 x7 &&& _loginto y0 x6 x8)) ) ) ) )
                  ||| ( y1 === disj x5 x6
                      &&& ( x5 === ltrue ()
                          &&& (__loginto y0 x6 ||| loginto y0 x6)
                          ||| ( x5 === lfalse () &&& loginto y0 x6
                              ||| ( x5 === var x396
                                  &&& ( x6 === ltrue () &&& __lookupoOro y0 x396 x7
                                      ||| ( x6 === lfalse () &&& ___lookupoOro y0 x396 x7
                                          ||| ( x6 === var x677
                                              &&& (__lookupoLookupo y0 x396 x677 ||| (___lookupoLookupo y0 x396 x677 ||| lookupoLookupo y0 x396 x677))
                                              ||| ( x6 === neg x676 &&& noto x680 x8
                                                  ||| ( x6 === conj x708 x710
                                                      &&& ( logintoLoginto y0 x708 x709 x710 x711
                                                          &&& (__oro x7 x8 &&& (__lookupo y0 x396 x7 &&& ando x709 x711 x8)) )
                                                      ||| ( x6 === disj x720 x722
                                                          &&& ( logintoLoginto y0 x720 x721 x722 x723
                                                              &&& (__oro x7 x8 &&& (__lookupo y0 x396 x7 &&& oro x721 x723 x8)) ) ) ) ) ) ) )
                                  ||| ( x5 === neg x395 &&& noto x399 x7
                                      ||| ( x5 === conj x397 x398
                                          &&& (ando x399 x400 x7 &&& _loginto y0 x6 x8)
                                          ||| (x5 === disj x397 x398 &&& (oro x399 x400 x7 &&& _loginto y0 x6 x8)) ) ) ) ) ) ) ) ) ) )
  and lookupo y2 y3 = fresh (x12 x11 x13) (y2 === pair y3 !!true % x13 ||| (y2 === pair x11 x12 % x13 &&& lookupo x13 y3))
  and _lookupo y4 y5 = fresh (x29 x28 x30) (y4 === pair y5 !!false % x30 ||| (y4 === pair x28 x29 % x30 &&& _lookupo x30 y5))
  and _loginto y6 y7 y8 =
    fresh (x78 x74 x77 x73 x64 x60 x63 x59 x53 x52 x38)
      ( y7 === ltrue () &&& (y8 === !!true)
      ||| ( y7 === lfalse () &&& (y8 === !!false)
          ||| ( y7 === var x38 &&& __lookupo y6 x38 y8
              ||| ( y7 === neg x52
                  &&& (_loginto y6 x52 x53 &&& noto x53 y8)
                  ||| ( y7 === conj x59 x63
                      &&& (_loginto y6 x59 x60 &&& (_loginto y6 x63 x64 &&& ando x60 x64 y8))
                      ||| (y7 === disj x73 x77 &&& (_loginto y6 x73 x74 &&& (_loginto y6 x77 x78 &&& oro x74 x78 y8))) ) ) ) ) )
  and __lookupo y9 y10 y11 = fresh (x47 x46 x48) (y9 === pair y10 y11 % x48 ||| (y9 === pair x46 x47 % x48 &&& __lookupo x48 y10 y11))
  and noto y12 y13 = y12 === !!true &&& (y13 === !!false) ||| (y12 === !!false &&& (y13 === !!true))
  and ando y14 y15 y16 =
    y14 === !!false &&& (y15 === !!false) &&& (y16 === !!false)
    ||| ( y14 === !!false &&& (y15 === !!true) &&& (y16 === !!false)
        ||| (y14 === !!true &&& (y15 === !!false) &&& (y16 === !!false) ||| (y14 === !!true &&& (y15 === !!true) &&& (y16 === !!true))) )
  and oro y17 y18 y19 =
    y17 === !!false &&& (y18 === !!false) &&& (y19 === !!false)
    ||| ( y17 === !!false &&& (y18 === !!true) &&& (y19 === !!true)
        ||| (y17 === !!true &&& (y18 === !!false) &&& (y19 === !!true) ||| (y17 === !!true &&& (y18 === !!true) &&& (y19 === !!true))) )
  and _noto y20 = y20 === !!false
  and logintoAndo y21 y22 y23 y24 y25 =
    fresh
      (x102 x140 x100 x139 x130 x131 x128 x99 x116 x115 x98)
      ( y22 === ltrue () &&& (y23 === !!true)
      &&& (y24 === !!false &&& (y25 === !!false) ||| (y24 === !!true &&& (y25 === !!true)))
      ||| ( y22 === lfalse () &&& (y23 === !!false)
          &&& (y24 === !!false &&& (y25 === !!false) ||| (y24 === !!true &&& (y25 === !!false)))
          ||| ( y22 === var x98
              &&& ( y24 === !!false &&& (y23 === !!false) &&& (y25 === !!false) &&& _lookupo y21 x98
                  ||| ( y24 === !!false &&& (y23 === !!true) &&& (y25 === !!false) &&& lookupo y21 x98
                      ||| ( y24 === !!true &&& (y23 === !!false) &&& (y25 === !!false) &&& _lookupo y21 x98
                          ||| (y24 === !!true &&& (y23 === !!true) &&& (y25 === !!true) &&& lookupo y21 x98) ) ) )
              ||| ( y22 === neg x115
                  &&& (_loginto y21 x115 x116 &&& (ando y24 y23 y25 &&& noto x116 y23))
                  ||| ( y22 === conj x99 x128
                      &&& (logintoAndo y21 x128 x131 x130 y23 &&& (_loginto y21 x128 x131 &&& ando y24 y23 y25))
                      ||| (y22 === disj x139 x100 &&& (_loginto y21 x139 x140 &&& (ando y24 y23 y25 &&& logintoOro y21 x100 x102 x140 y23))) ) ) ) ) )
  and logintoOro y26 y27 y28 y29 y30 =
    fresh (x193 x194 x191 x177 x178 x175 x148 x165 x164 x147)
      ( y27 === ltrue () &&& (y28 === !!true)
      &&& (y29 === !!false &&& (y30 === !!true) ||| (y29 === !!true &&& (y30 === !!true)))
      ||| ( y27 === lfalse () &&& (y28 === !!false)
          &&& (y29 === !!false &&& (y30 === !!false) ||| (y29 === !!true &&& (y30 === !!true)))
          ||| ( y27 === var x147
              &&& ( y29 === !!false &&& (y28 === !!false) &&& (y30 === !!false) &&& _lookupo y26 x147
                  ||| ( y29 === !!false &&& (y28 === !!true) &&& (y30 === !!true) &&& lookupo y26 x147
                      ||| ( y29 === !!true &&& (y28 === !!false) &&& (y30 === !!true) &&& _lookupo y26 x147
                          ||| (y29 === !!true &&& (y28 === !!true) &&& (y30 === !!true) &&& lookupo y26 x147) ) ) )
              ||| ( y27 === neg x164
                  &&& (_loginto y26 x164 x165 &&& (oro y29 y28 y30 &&& noto x165 y28))
                  ||| ( y27 === conj x148 x175
                      &&& (logintoAndo y26 x175 x178 x177 y28 &&& (_loginto y26 x175 x178 &&& oro y29 y28 y30))
                      ||| (y27 === disj x148 x191 &&& (logintoOro y26 x191 x194 x193 y28 &&& (_loginto y26 x191 x194 &&& oro y29 y28 y30))) ) ) ) ) )
  and lookupoAndo y31 y32 y33 =
    fresh (x228 x227 x229) (y31 === pair y32 y33 % x229 &&& (y33 === !!true) ||| (y31 === pair x227 x228 % x229 &&& lookupoAndo x229 y32 y33))
  and _lookupoAndo y34 y35 y36 = fresh (x236 x235 x234) (y34 === pair x234 x235 % x236 &&& _lookupoAndo x236 y35 y36)
  and lookupoLookupo y37 y38 y39 =
    fresh (x252 x251 x242 x241 x243)
      ( y37
      === pair y38 !!true % x243
      &&& (y39 === y38 ||| lookupo x243 y39)
      ||| (y37 === pair x241 x242 % x251 &&& (x252 === pair x241 x242 % x251 &&& lookupo x251 y38 &&& (x252 === pair x241 x242 % x251 &&& lookupo x252 y39)))
      )
  and logintoLoginto y40 y41 y42 y43 y44 =
    fresh
      (x341 x339 x340 x338 x329 x327 x328 x326 x322 x321 x268)
      ( y41 === ltrue () &&& (y42 === !!true) &&& _loginto y40 y43 y44
      ||| ( y41 === lfalse () &&& (y42 === !!false) &&& _loginto y40 y43 y44
          ||| ( y41 === var x268 &&& lookupoLoginto y40 x268 y42 y43 y44
              ||| ( y41 === neg x321
                  &&& (logintoLoginto y40 x321 x322 y43 y44 &&& noto x322 y42)
                  ||| ( y41 === conj x326 x328
                      &&& (logintoLoginto y40 x326 x327 x328 x329 &&& (ando x327 x329 y42 &&& _loginto y40 y43 y44))
                      ||| (y41 === disj x338 x340 &&& (logintoLoginto y40 x338 x339 x340 x341 &&& (oro x339 x341 y42 &&& _loginto y40 y43 y44))) ) ) ) ) )
  and lookupoLoginto y45 y46 y47 y48 y49 =
    fresh
      (x316 x314 x315 x313 x308 x306 x307 x305 x301 x300 x295 x296 x286 x285 x287 x277)
      ( y48 === ltrue () &&& (y49 === !!true) &&& __lookupo y45 y46 y47
      ||| ( y48 === lfalse () &&& (y49 === !!false) &&& __lookupo y45 y46 y47
          ||| ( y48 === var x277
              &&& ( y45
                  === pair x277 y49 % x287
                  &&& (y46 === x277 &&& (y47 === y49) ||| __lookupo x287 y46 y47)
                  ||| ( y45
                      === pair x285 x286 % x296
                      &&& (x295 === pair x285 x286 % x296 &&& __lookupo x295 y46 y47 &&& (x295 === pair x285 x286 % x296 &&& __lookupo x296 x277 y49)) ) )
              ||| ( y48 === neg x300
                  &&& (lookupoLoginto y45 y46 y47 x300 x301 &&& noto x301 y49)
                  ||| ( y48 === conj x305 x307
                      &&& (logintoLoginto y45 x305 x306 x307 x308 &&& (__lookupo y45 y46 y47 &&& ando x306 x308 y49))
                      ||| (y48 === disj x313 x315 &&& (logintoLoginto y45 x313 x314 x315 x316 &&& (__lookupo y45 y46 y47 &&& oro x314 x316 y49))) ) ) ) ) )
  and _ando y50 y51 = y50 === !!true &&& (y51 === !!true)
  and __loginto y52 y53 =
    fresh
      (x589 x587 x586 x588 x584 x635 x633 x634 x632 x625 x623 x624 x622 x598 x594 x595 x585 x452 x450 x449 x451 x447 x546 x544 x545 x543 x534 x532 x533 x531
         x408 x463 x459 x460 x448 x406 x405 x440 x439 x417 x432 x415 x431 x407 x425 x424 x413 x403 x404)
      ( y53 === lfalse ()
      ||| ( y53 === var x404 &&& _lookupo y52 x404
          ||| ( y53 === neg x403
              &&& ( x403 === ltrue ()
                  ||| ( x403 === var x413 &&& lookupo y52 x413
                      ||| ( x403 === neg x424
                          &&& (_loginto y52 x424 x425 &&& (__noto x407 &&& noto x425 x407))
                          ||| ( x403 === conj x431 x415
                              &&& (_loginto y52 x431 x432 &&& (__noto x407 &&& logintoAndo y52 x415 x417 x432 x407))
                              ||| (x403 === disj x439 x415 &&& (_loginto y52 x439 x440 &&& (__noto x407 &&& logintoOro y52 x415 x417 x440 x407))) ) ) ) )
              ||| ( y53 === conj x405 x406
                  &&& ( x405 === ltrue () &&& __loginto y52 x406
                      ||| ( x405 === lfalse ()
                          &&& (__loginto y52 x406 ||| loginto y52 x406)
                          ||| ( x405 === var x448
                              &&& ( x406 === ltrue () &&& __lookupoAndo y52 x448 x407
                                  ||| ( x406 === lfalse () &&& ___lookupoAndo y52 x448 x407
                                      ||| ( x406 === var x460
                                          &&& (_lookupoLookupo y52 x448 x460 ||| (__lookupoLookupo y52 x448 x460 ||| ___lookupoLookupo y52 x448 x460))
                                          ||| ( x406 === neg x459 &&& noto x463 x408
                                              ||| ( x406 === conj x531 x533
                                                  &&& ( logintoLoginto y52 x531 x532 x533 x534
                                                      &&& (__ando x407 x408 &&& (__lookupo y52 x448 x407 &&& ando x532 x534 x408)) )
                                                  ||| ( x406 === disj x543 x545
                                                      &&& ( logintoLoginto y52 x543 x544 x545 x546
                                                          &&& (__ando x407 x408 &&& (__lookupo y52 x448 x407 &&& oro x544 x546 x408)) ) ) ) ) ) ) )
                              ||| ( x405 === neg x447 &&& noto x451 x407
                                  ||| ( x405 === conj x449 x450
                                      &&& (ando x451 x452 x407 &&& _loginto y52 x406 x408)
                                      ||| (x405 === disj x449 x450 &&& (oro x451 x452 x407 &&& _loginto y52 x406 x408)) ) ) ) ) )
                  ||| ( y53 === disj x405 x406
                      &&& ( x405 === lfalse () &&& __loginto y52 x406
                          ||| ( x405 === var x585
                              &&& ( x406 === ltrue () &&& lookupoOro y52 x585 x407
                                  ||| ( x406 === lfalse () &&& _lookupoOro y52 x585 x407
                                      ||| ( x406 === var x595 &&& _lookupoLookupo y52 x585 x595
                                          ||| ( x406 === neg x594 &&& noto x598 x408
                                              ||| ( x406 === conj x622 x624
                                                  &&& ( logintoLoginto y52 x622 x623 x624 x625
                                                      &&& (_oro x407 x408 &&& (__lookupo y52 x585 x407 &&& ando x623 x625 x408)) )
                                                  ||| ( x406 === disj x632 x634
                                                      &&& ( logintoLoginto y52 x632 x633 x634 x635
                                                          &&& (_oro x407 x408 &&& (__lookupo y52 x585 x407 &&& oro x633 x635 x408)) ) ) ) ) ) ) )
                              ||| ( x405 === neg x584 &&& noto x588 x407
                                  ||| ( x405 === conj x586 x587
                                      &&& (ando x588 x589 x407 &&& _loginto y52 x406 x408)
                                      ||| (x405 === disj x586 x587 &&& (oro x588 x589 x407 &&& _loginto y52 x406 x408)) ) ) ) ) ) ) ) ) )
  and __noto y54 = y54 === !!true
  and __lookupoAndo y55 y56 y57 =
    fresh (x467 x466 x468) (y55 === pair y56 y57 % x468 &&& (y57 === !!false) ||| (y55 === pair x466 x467 % x468 &&& __lookupoAndo x468 y56 y57))
  and ___lookupoAndo y58 y59 y60 =
    fresh (x474 x473 x475)
      (y58 === pair y59 y60 % x475 &&& (y60 === !!false ||| (y60 === !!true)) ||| (y58 === pair x473 x474 % x475 &&& ___lookupoAndo x475 y59 y60))
  and _lookupoLookupo y61 y62 y63 =
    fresh (x493 x492 x483 x482 x484)
      ( y61
      === pair y62 !!false % x484
      &&& (y63 === y62 ||| _lookupo x484 y63)
      ||| (y61 === pair x482 x483 % x492 &&& (x493 === pair x482 x483 % x492 &&& _lookupo x492 y62 &&& (x493 === pair x482 x483 % x492 &&& _lookupo x493 y63)))
      )
  and __lookupoLookupo y64 y65 y66 =
    fresh (x507 x506 x498 x497 x499)
      ( y64
      === pair y65 !!false % x499
      &&& lookupo x499 y66
      ||| (y64 === pair x497 x498 % x506 &&& (x507 === pair x497 x498 % x506 &&& _lookupo x506 y65 &&& (x507 === pair x497 x498 % x506 &&& lookupo x507 y66)))
      )
  and ___lookupoLookupo y67 y68 y69 =
    fresh (x521 x520 x512 x511 x513)
      ( y67
      === pair y68 !!true % x513
      &&& _lookupo x513 y69
      ||| (y67 === pair x511 x512 % x520 &&& (x521 === pair x511 x512 % x520 &&& lookupo x520 y68 &&& (x521 === pair x511 x512 % x520 &&& _lookupo x521 y69)))
      )
  and __ando y70 y71 = y70 === !!false &&& (y71 === !!false) ||| (y70 === !!false &&& (y71 === !!true) ||| (y70 === !!true &&& (y71 === !!false)))
  and lookupoOro y72 y73 y74 = fresh (x603 x602 x601) (y72 === pair x601 x602 % x603 &&& lookupoOro x603 y73 y74)
  and _lookupoOro y75 y76 y77 =
    fresh (x608 x607 x609) (y75 === pair y76 y77 % x609 &&& (y77 === !!false) ||| (y75 === pair x607 x608 % x609 &&& _lookupoOro x609 y76 y77))
  and _oro y78 y79 = y78 === !!false &&& (y79 === !!false)
  and __lookupoOro y80 y81 y82 =
    fresh (x684 x683 x685)
      (y80 === pair y81 y82 % x685 &&& (y82 === !!false ||| (y82 === !!true)) ||| (y80 === pair x683 x684 % x685 &&& __lookupoOro x685 y81 y82))
  and ___lookupoOro y83 y84 y85 =
    fresh (x692 x691 x693) (y83 === pair y84 y85 % x693 &&& (y85 === !!true) ||| (y83 === pair x691 x692 % x693 &&& ___lookupoOro x693 y84 y85))
  and __oro y86 y87 = y86 === !!false &&& (y87 === !!true) ||| (y86 === !!true &&& (y87 === !!false) ||| (y86 === !!true &&& (y87 === !!true))) in
  loginto x0 x1



(*

( y1 === disj x5 x6 &&& 
      
      ----------- ( x5 === ltrue () &&& (__loginto y0 x6 ||| loginto y0 x6)
      ||| 
      ----------- ( x5 === lfalse () &&& loginto y0 x6
      ||| 
      ----------- ( x5 === var x396 &&& ( x6 === ltrue () &&& __lookupoOro y0 x396 x7
      ||| 

      ----------- ( x6 === lfalse () &&& ___lookupoOro y0 x396 x7
                  ||| ( x6 === var x677
                      &&& (__lookupoLookupo y0 x396 x677 ||| (___lookupoLookupo y0 x396 x677 ||| lookupoLookupo y0 x396 x677))
                      ||| ( x6 === neg x676 &&& noto x680 x8
                          ||| ( x6 === conj x708 x710
                              &&& ( logintoLoginto y0 x708 x709 x710 x711
                                  &&& (__oro x7 x8 &&& (__lookupo y0 x396 x7 &&& ando x709 x711 x8)) )
                              ||| ( x6 === disj x720 x722
                                  &&& ( logintoLoginto y0 x720 x721 x722 x723
                                      &&& (__oro x7 x8 &&& (__lookupo y0 x396 x7 &&& oro x721 x723 x8)) ) ) ) ) ) ) )

      ||| ( x5 === neg x395 &&& noto x399 x7
      ||| ( x5 === conj x397 x398 &&& (ando x399 x400 x7 &&& _loginto y0 x6 x8)
      ||| (x5 === disj x397 x398 &&& (oro x399 x400 x7 &&& _loginto y0 x6 x8)) ) ) ) ) ) )

*)
