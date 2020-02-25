open GT
open OCanren
open Std
open Nat

open LogicExpr

let maxuLogint x0 x1 =
  let rec loginto y0 y1 =
    fresh
      (x3731 x3729 x3728 x3730 x3726 x3914 x3912 x3913 x3911 x3905 x3903 x3904 x3902 x3849 x3847 x3846 x3848 x3844 x3885 x3884 x3879 x3878 x3880 x3810 x3874
         x3873 x3863 x3862 x3864 x3845 x3806 x3839 x3838 x3834 x3833 x3835 x3829 x3828 x3820 x3819 x3821 x3807 x3727 x3799 x3798 x3776 x3791 x3774 x3790 x3784
         x3783 x3772 x3764 x3763 x3738 x3756 x3736 x3755 x3748 x3747 x3734 x219 x217 x216 x218 x214 x3688 x3686 x3687 x3685 x3629 x3627 x3628 x3626 x319 x317
         x316 x318 x314 x292 x315 x288 x289 x215 x281 x280 x261 x273 x259 x272 x267 x266 x249 x248 x226 x241 x224 x240 x8 x234 x233 x222 x6 x5 x207 x206 x22
         x90 x20 x89 x35 x34 x7 x18 x3 x4)
      ( y1 === ltrue ()
      ||| ( y1 === var x4 &&& lookupo y0 x4
          ||| ( y1 === neg x3
              &&& ( x3 === lfalse ()
                  ||| ( x3 === var x18 &&& lookupoNoto y0 x18 x7
                      ||| ( x3 === neg x34
                          &&& (_loginto y0 x34 x35 &&& (noto x7 &&& _noto x35 x7))
                          ||| ( x3 === conj x89 x20
                              &&& (_loginto y0 x89 x90 &&& (noto x7 &&& logintoAndo y0 x20 x22 x90 x7))
                              ||| (x3 === disj x206 x20 &&& (_loginto y0 x206 x207 &&& (noto x7 &&& logintoOro y0 x20 x22 x207 x7))) ) ) ) )
              ||| ( y1 === conj x5 x6
                  &&& ( x5 === ltrue ()
                      &&& ( x6 === ltrue ()
                          ||| ( x6 === var x222 &&& lookupo y0 x222
                              ||| ( x6 === neg x233
                                  &&& (_loginto y0 x233 x234 &&& (_ando x8 &&& _noto x234 x8))
                                  ||| ( x6 === conj x240 x224
                                      &&& (_loginto y0 x240 x241 &&& (_ando x8 &&& logintoAndo y0 x224 x226 x241 x8))
                                      ||| (x6 === disj x248 x224 &&& (_loginto y0 x248 x249 &&& (_ando x8 &&& logintoOro y0 x224 x226 x249 x8))) ) ) ) )
                      ||| ( x5 === lfalse ()
                          &&& ( x6 === neg x266
                              &&& (_loginto y0 x266 x267 &&& _noto x267 x8)
                              ||| ( x6 === conj x272 x259
                                  &&& (_loginto y0 x272 x273 &&& logintoAndo y0 x259 x261 x273 x8)
                                  ||| (x6 === disj x280 x259 &&& (_loginto y0 x280 x281 &&& logintoOro y0 x259 x261 x281 x8)) ) )
                          ||| ( x5 === var x215
                              &&& ( x6 === ltrue () &&& lookupo y0 x215
                                  ||| ( x6 === var x289 &&& lookupoLookupo y0 x289 x215
                                      ||| ( x6 === neg x288
                                          &&& ( x288 === lfalse () &&& notoLookupo y0 x215
                                              ||| ( x288 === var x315 &&& lookupoNotoLookupo y0 x315 x292 x215
                                                  ||| ( x288 === neg x314
                                                      &&& (logintoNotoNotoLookupo y0 x314 x318 x292 x8 x215 x7 &&& __ando x7 x8)
                                                      ||| ( x288 === conj x316 x317
                                                          &&& (logintoLogintoAndoNotoLookupo y0 x316 x318 x317 x319 x292 x8 x215 x7 &&& __ando x7 x8)
                                                          ||| ( x288 === disj x316 x317
                                                              &&& (logintoLogintoOroNotoLookupo y0 x316 x318 x317 x319 x292 x8 x215 x7 &&& __ando x7 x8) ) ) )
                                                  ) )
                                          ||| ( x6 === conj x3626 x3628
                                              &&& ( logintoLoginto y0 x3626 x3627 x3628 x3629
                                                  &&& (__ando x7 x8 &&& (ando x3627 x3629 x8 &&& _lookupo y0 x215 x7)) )
                                              ||| ( x6 === disj x3685 x3687
                                                  &&& ( logintoLoginto y0 x3685 x3686 x3687 x3688
                                                      &&& (__ando x7 x8 &&& (oro x3686 x3688 x8 &&& _lookupo y0 x215 x7)) ) ) ) ) ) )
                              ||| ( x5 === neg x214 &&& _noto x218 x7
                                  ||| ( x5 === conj x216 x217
                                      &&& (ando x218 x219 x7 &&& _loginto y0 x6 x8)
                                      ||| (x5 === disj x216 x217 &&& (oro x218 x219 x7 &&& _loginto y0 x6 x8)) ) ) ) ) )
                  ||| ( y1 === disj x5 x6
                      &&& ( x5 === ltrue ()
                          &&& ( x6 === ltrue ()
                              ||| ( x6 === lfalse ()
                                  ||| ( x6 === var x3734
                                      &&& (__lookupo y0 x3734 ||| lookupo y0 x3734)
                                      ||| ( x6 === neg x3747
                                          &&& (_loginto y0 x3747 x3748 &&& (___oro x8 &&& _noto x3748 x8))
                                          ||| ( x6 === conj x3755 x3736
                                              &&& (_loginto y0 x3755 x3756 &&& (___oro x8 &&& logintoAndo y0 x3736 x3738 x3756 x8))
                                              ||| (x6 === disj x3763 x3736 &&& (_loginto y0 x3763 x3764 &&& (___oro x8 &&& logintoOro y0 x3736 x3738 x3764 x8)))
                                              ) ) ) ) )
                          ||| ( x5 === lfalse ()
                              &&& ( x6 === ltrue ()
                                  ||| ( x6 === var x3772 &&& lookupo y0 x3772
                                      ||| ( x6 === neg x3783
                                          &&& (_loginto y0 x3783 x3784 &&& (____oro x8 &&& _noto x3784 x8))
                                          ||| ( x6 === conj x3790 x3774
                                              &&& (_loginto y0 x3790 x3791 &&& (____oro x8 &&& logintoAndo y0 x3774 x3776 x3791 x8))
                                              ||| ( x6 === disj x3798 x3774
                                                  &&& (_loginto y0 x3798 x3799 &&& (____oro x8 &&& logintoOro y0 x3774 x3776 x3799 x8)) ) ) ) ) )
                              ||| ( x5 === var x3727
                                  &&& ( x6 === ltrue ()
                                      &&& (__lookupo y0 x3727 ||| lookupo y0 x3727)
                                      ||| ( x6 === lfalse () &&& lookupo y0 x3727
                                          ||| ( x6 === var x3807
                                              &&& ( y0
                                                  === pair x3807 !!true % x3821
                                                  &&& __lookupo x3821 x3727
                                                  ||| ( y0
                                                      === pair x3819 x3820 % x3828
                                                      &&& ( x3829
                                                          === pair x3819 x3820 % x3828
                                                          &&& lookupo x3828 x3807
                                                          &&& (x3829 === pair x3819 x3820 % x3828 &&& __lookupo x3829 x3727) ) )
                                                  ||| ( y0
                                                      === pair x3807 !!false % x3835
                                                      &&& ____lookupo x3807 x3835 x3727
                                                      ||| ( y0
                                                          === pair x3833 x3834 % x3838
                                                          &&& ( x3839
                                                              === pair x3833 x3834 % x3838
                                                              &&& __lookupo x3838 x3807
                                                              &&& (x3839 === pair x3833 x3834 % x3838 &&& lookupo x3839 x3727) ) )
                                                      ||| lookupoLookupo y0 x3807 x3727 ) )
                                              ||| ( x6 === neg x3806
                                                  &&& ( x3806 === ltrue () &&& lookupo y0 x3727
                                                      ||| ( x3806 === lfalse ()
                                                          &&& (__lookupo y0 x3727 ||| notoLookupo y0 x3727)
                                                          ||| ( x3806 === var x3845
                                                              &&& ( y0
                                                                  === pair x3845 !!false % x3864
                                                                  &&& (x3727 === x3845 ||| __lookupo x3864 x3727)
                                                                  ||| ( y0
                                                                      === pair x3862 x3863 % x3873
                                                                      &&& ( x3874
                                                                          === pair x3862 x3863 % x3873
                                                                          &&& lookupoNoto x3873 x3845 x3810
                                                                          &&& (x3874 === pair x3862 x3863 % x3873 &&& __lookupo x3874 x3727) ) )
                                                                  ||| ( y0
                                                                      === pair x3845 !!true % x3880
                                                                      &&& ___lookupo x3845 x3880 x3727
                                                                      ||| ( y0
                                                                          === pair x3878 x3879 % x3884
                                                                          &&& ( x3885
                                                                              === pair x3878 x3879 % x3884
                                                                              &&& _lookupoNoto x3884 x3845 x3810
                                                                              &&& (x3885 === pair x3878 x3879 % x3884 &&& lookupo x3885 x3727) ) )
                                                                      ||| lookupoNotoLookupo y0 x3845 x3810 x3727 ) )
                                                              ||| ( x3806 === neg x3844
                                                                  &&& (logintoNotoNotoLookupo y0 x3844 x3848 x3810 x8 x3727 x7 &&& _____oro x7 x8)
                                                                  ||| ( x3806 === conj x3846 x3847
                                                                      &&& ( logintoLogintoAndoNotoLookupo y0 x3846 x3848 x3847 x3849 x3810 x8 x3727 x7
                                                                          &&& _____oro x7 x8 )
                                                                      ||| ( x3806 === disj x3846 x3847
                                                                          &&& ( logintoLogintoOroNotoLookupo y0 x3846 x3848 x3847 x3849 x3810 x8 x3727 x7
                                                                              &&& _____oro x7 x8 ) ) ) ) ) ) )
                                                  ||| ( x6 === conj x3902 x3904
                                                      &&& ( logintoLoginto y0 x3902 x3903 x3904 x3905
                                                          &&& (_____oro x7 x8 &&& (ando x3903 x3905 x8 &&& _lookupo y0 x3727 x7)) )
                                                      ||| ( x6 === disj x3911 x3913
                                                          &&& ( logintoLoginto y0 x3911 x3912 x3913 x3914
                                                              &&& (_____oro x7 x8 &&& (oro x3912 x3914 x8 &&& _lookupo y0 x3727 x7)) ) ) ) ) ) ) )
                                  ||| ( x5 === neg x3726 &&& _noto x3730 x7
                                      ||| ( x5 === conj x3728 x3729
                                          &&& (ando x3730 x3731 x7 &&& _loginto y0 x6 x8)
                                          ||| (x5 === disj x3728 x3729 &&& (oro x3730 x3731 x7 &&& _loginto y0 x6 x8)) ) ) ) ) ) ) ) ) ) )
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
    fresh (x101 x144 x99 x143 x134 x135 x132 x98 x120 x119 x97)
      ( y23 === ltrue () &&& (y24 === !!true)
      &&& (y25 === !!false &&& (y26 === !!false) ||| (y25 === !!true &&& (y26 === !!true)))
      ||| ( y23 === lfalse () &&& (y24 === !!false)
          &&& (y25 === !!false &&& (y26 === !!false) ||| (y25 === !!true &&& (y26 === !!false)))
          ||| ( y23 === var x97
              &&& ( y25 === !!false &&& (y24 === !!false) &&& (y26 === !!false) &&& __lookupo y22 x97
                  ||| ( y25 === !!false &&& (y24 === !!true) &&& (y26 === !!false) &&& lookupo y22 x97
                      ||| ( y25 === !!true &&& (y24 === !!false) &&& (y26 === !!false) &&& __lookupo y22 x97
                          ||| (y25 === !!true &&& (y24 === !!true) &&& (y26 === !!true) &&& lookupo y22 x97) ) ) )
              ||| ( y23 === neg x119
                  &&& (_loginto y22 x119 x120 &&& (ando y25 y24 y26 &&& _noto x120 y24))
                  ||| ( y23 === conj x98 x132
                      &&& (logintoAndo y22 x132 x135 x134 y24 &&& (_loginto y22 x132 x135 &&& ando y25 y24 y26))
                      ||| (y23 === disj x143 x99 &&& (_loginto y22 x143 x144 &&& (ando y25 y24 y26 &&& logintoOro y22 x99 x101 x144 y24))) ) ) ) ) )
  and __lookupo y27 y28 = fresh (x111 x110 x112) (y27 === pair y28 !!false % x112 ||| (y27 === pair x110 x111 % x112 &&& __lookupo x112 y28))
  and logintoOro y29 y30 y31 y32 y33 =
    fresh (x197 x198 x195 x181 x182 x179 x152 x169 x168 x151)
      ( y30 === ltrue () &&& (y31 === !!true)
      &&& (y32 === !!false &&& (y33 === !!true) ||| (y32 === !!true &&& (y33 === !!true)))
      ||| ( y30 === lfalse () &&& (y31 === !!false)
          &&& (y32 === !!false &&& (y33 === !!false) ||| (y32 === !!true &&& (y33 === !!true)))
          ||| ( y30 === var x151
              &&& ( y32 === !!false &&& (y31 === !!false) &&& (y33 === !!false) &&& __lookupo y29 x151
                  ||| ( y32 === !!false &&& (y31 === !!true) &&& (y33 === !!true) &&& lookupo y29 x151
                      ||| ( y32 === !!true &&& (y31 === !!false) &&& (y33 === !!true) &&& __lookupo y29 x151
                          ||| (y32 === !!true &&& (y31 === !!true) &&& (y33 === !!true) &&& lookupo y29 x151) ) ) )
              ||| ( y30 === neg x168
                  &&& (_loginto y29 x168 x169 &&& (oro y32 y31 y33 &&& _noto x169 y31))
                  ||| ( y30 === conj x152 x179
                      &&& (logintoAndo y29 x179 x182 x181 y31 &&& (_loginto y29 x179 x182 &&& oro y32 y31 y33))
                      ||| (y30 === disj x152 x195 &&& (logintoOro y29 x195 x198 x197 y31 &&& (_loginto y29 x195 x198 &&& oro y32 y31 y33))) ) ) ) ) )
  and _ando y34 = y34 === !!true
  and lookupoLookupo y35 y36 y37 =
    fresh (x310 x309 x300 x299 x301)
      ( y35
      === pair y36 !!true % x301
      &&& ___lookupo y36 x301 y37
      ||| (y35 === pair x299 x300 % x309 &&& (x310 === pair x299 x300 % x309 &&& lookupo x309 y36 &&& (x310 === pair x299 x300 % x309 &&& lookupo x310 y37)))
      )
  and ___lookupo y38 y39 y40 = y40 === y38 ||| lookupo y39 y40
  and notoLookupo y41 y42 = lookupo y41 y42
  and lookupoNotoLookupo y43 y44 y45 y46 =
    fresh (x338 x337 x328 x327 x329)
      ( y43
      === pair y44 y45 % x329
      &&& (y45 === !!false &&& ____lookupo y44 x329 y46)
      ||| ( y43
          === pair x327 x328 % x337
          &&& (x338 === pair x327 x328 % x337 &&& lookupoNoto x337 y44 y45 &&& (x338 === pair x327 x328 % x337 &&& lookupo x338 y46)) ) )
  and ____lookupo y47 y48 y49 = lookupo y48 y49
  and logintoNotoNotoLookupo y50 y51 y52 y53 y54 y55 y56 =
    fresh
      (x455 x454 x348 x405 x346 x404 x391 x389 x376 x375 x357 x356 x358 x344)
      ( y51 === ltrue () &&& (y52 === !!true)
      &&& (y53 === !!false &&& _notoLookupo y54 y50 y55 y56)
      ||| ( y51 === lfalse () &&& (y52 === !!false)
          &&& (y53 === !!true &&& __notoLookupo y54 y50 y55 y56)
          ||| ( y51 === var x344
              &&& ( y50
                  === pair x344 y52 % x358
                  &&& ( y52 === !!true &&& (y53 === !!false) &&& ___notoLookupo y54 x344 x358 y55 y56
                      ||| (y52 === !!false &&& (y53 === !!true) &&& ____notoLookupo y54 x344 x358 y55 y56) )
                  ||| ( y50
                      === pair x356 x357 % x375
                      &&& ( x376
                          === pair x356 x357 % x375
                          &&& lookupoNotoNoto x375 x344 y52 y53 y54
                          &&& (x376 === pair x356 x357 % x375 &&& _lookupo x376 y55 y56) ) ) )
              ||| ( y51 === neg x389
                  &&& (logintoNotoNotoLookupo y50 x389 x391 y52 y53 y55 y56 &&& _noto y53 y54)
                  ||| ( y51 === conj x404 x346
                      &&& (logintoLookupo y50 x404 x405 y55 y56 &&& (notoNoto y52 y53 y54 &&& logintoAndo y50 x346 x348 x405 y52))
                      ||| (y51 === disj x454 x346 &&& (logintoLookupo y50 x454 x455 y55 y56 &&& (notoNoto y52 y53 y54 &&& logintoOro y50 x346 x348 x455 y52)))
                      ) ) ) ) )
  and _notoLookupo y57 y58 y59 y60 = y57 === !!true &&& _lookupo y58 y59 y60
  and __notoLookupo y61 y62 y63 y64 = y61 === !!false &&& _lookupo y62 y63 y64
  and ___notoLookupo y65 y66 y67 y68 y69 = y65 === !!true &&& _____lookupo y66 y67 y68 y69
  and _____lookupo y70 y71 y72 y73 = y72 === y70 &&& (y73 === !!true) ||| _lookupo y71 y72 y73
  and ____notoLookupo y74 y75 y76 y77 y78 = y74 === !!false &&& ______lookupo y75 y76 y77 y78
  and ______lookupo y79 y80 y81 y82 = y81 === y79 &&& (y82 === !!false) ||| _lookupo y80 y81 y82
  and lookupoNotoNoto y83 y84 y85 y86 y87 =
    fresh (x379 x378 x380) (y83 === pair y84 y85 % x380 &&& notoNoto y85 y86 y87 ||| (y83 === pair x378 x379 % x380 &&& lookupoNotoNoto x380 y84 y85 y86 y87))
  and notoNoto y88 y89 y90 = y88 === !!true &&& (y89 === !!false) &&& __noto y90 ||| (y88 === !!false &&& (y89 === !!true) &&& ___noto y90)
  and __noto y91 = y91 === !!true
  and ___noto y92 = y92 === !!false
  and logintoLookupo y93 y94 y95 y96 y97 =
    fresh (x414 x412 x411 x413 x409 x410)
      ( y94 === ltrue () &&& (y95 === !!true) &&& _lookupo y93 y96 y97
      ||| ( y94 === lfalse () &&& (y95 === !!false) &&& _lookupo y93 y96 y97
          ||| ( y94 === var x410 &&& _lookupoLookupo y93 x410 y95 y96 y97
              ||| ( y94 === neg x409 &&& logintoNotoLookupo y93 x409 x413 y95 y96 y97
                  ||| ( y94 === conj x411 x412
                      &&& logintoLogintoAndoLookupo y93 x411 x413 x412 x414 y95 y96 y97
                      ||| (y94 === disj x411 x412 &&& logintoLogintoOroLookupo y93 x411 x413 x412 x414 y95 y96 y97) ) ) ) ) )
  and _lookupoLookupo y98 y99 y100 y101 y102 =
    fresh (x419 x418 x420)
      ( y98
      === pair y99 y100 % x420
      &&& _______lookupo y99 y100 x420 y101 y102
      ||| (y98 === pair x418 x419 % x420 &&& __lookupoLookupo x420 y99 y100 x418 x419 y101 y102) )
  and _______lookupo y103 y104 y105 y106 y107 = y106 === y103 &&& (y107 === y104) ||| _lookupo y105 y106 y107
  and __lookupoLookupo y108 y109 y110 y111 y112 y113 y114 =
    fresh (x429) (x429 === pair y111 y112 % y108 &&& _lookupo y108 y109 y110 &&& (x429 === pair y111 y112 % y108 &&& _lookupo x429 y113 y114))
  and logintoNotoLookupo y115 y116 y117 y118 y119 y120 = logintoLookupo y115 y116 y117 y119 y120 &&& _noto y117 y118
  and logintoLogintoAndoLookupo y121 y122 y123 y124 y125 y126 y127 y128 = logintoLookupo y121 y122 y123 y127 y128 &&& logintoAndo y121 y124 y125 y123 y126
  and logintoLogintoOroLookupo y129 y130 y131 y132 y133 y134 y135 y136 = logintoLookupo y129 y130 y131 y135 y136 &&& logintoOro y129 y132 y133 y131 y134
  and __ando y137 y138 = y137 === !!true &&& (y138 === !!true)
  and logintoLogintoAndoNotoLookupo y139 y140 y141 y142 y143 y144 y145 y146 y147 =
    fresh
      (x470 x468 x467 x2877 x2876 x2874 x2872 x469 x465 x2810 x2808 x2809 x2807 x2793 x2792 x2790 x2788 x950 x948 x947 x1259 x1257 x1256 x1261 x1254 x1252 x949
         x945 x1014 x1013 x1024 x1023 x1025 x1015 x994 x993 x995 x613 x946 x609 x795 x794 x803 x802 x804 x796 x713 x712 x714 x610 x466 x564 x602 x562 x601 x593
         x592 x590 x588 x581 x580 x560 x477 x552 x475 x551 x543 x542 x540 x538 x531 x530 x473)
      ( y140 === ltrue () &&& (y141 === !!true)
      &&& ( y142 === ltrue () &&& (y143 === !!true)
          &&& (y144 === !!true &&& __notoLookupo y145 y139 y146 y147)
          ||| ( y142 === lfalse () &&& (y143 === !!false)
              &&& (y144 === !!false &&& _notoLookupo y145 y139 y146 y147)
              ||| ( y142 === var x473
                  &&& ( y143 === !!false &&& (y144 === !!false) &&& _lookupoNotoLookupo y139 x473 y145 y146 y147
                      ||| (y143 === !!true &&& (y144 === !!true) &&& __lookupoNotoLookupo y139 x473 y145 y146 y147) )
                  ||| ( y142 === neg x530
                      &&& (logintoLookupo y139 x530 x531 y146 y147 &&& (andoNoto y143 y144 y145 &&& _noto x531 y143))
                      ||| ( y142 === conj x538 x540
                          &&& (logintoLogintoAndoLookupo y139 x538 x542 x540 x543 y143 y146 y147 &&& (_noto y144 y145 &&& ___ando y143 y144))
                          ||| ( y142 === disj x551 x475
                              &&& (logintoLookupo y139 x551 x552 y146 y147 &&& (andoNoto y143 y144 y145 &&& logintoOro y139 x475 x477 x552 y143)) ) ) ) ) ) )
      ||| ( y140 === lfalse () &&& (y141 === !!false)
          &&& ( y142 === ltrue () &&& (y143 === !!true)
              &&& (y144 === !!false &&& _notoLookupo y145 y139 y146 y147)
              ||| ( y142 === lfalse () &&& (y143 === !!false)
                  &&& (y144 === !!false &&& _notoLookupo y145 y139 y146 y147)
                  ||| ( y142 === var x560
                      &&& ( y143 === !!false &&& (y144 === !!false) &&& _lookupoNotoLookupo y139 x560 y145 y146 y147
                          ||| (y143 === !!true &&& (y144 === !!false) &&& ___lookupoNotoLookupo y139 x560 y145 y146 y147) )
                      ||| ( y142 === neg x580
                          &&& (logintoLookupo y139 x580 x581 y146 y147 &&& (_andoNoto y143 y144 y145 &&& _noto x581 y143))
                          ||| ( y142 === conj x588 x590
                              &&& (logintoLogintoAndoLookupo y139 x588 x592 x590 x593 y143 y146 y147 &&& (_noto y144 y145 &&& ____ando y143 y144))
                              ||| ( y142 === disj x601 x562
                                  &&& (logintoLookupo y139 x601 x602 y146 y147 &&& (_andoNoto y143 y144 y145 &&& logintoOro y139 x562 x564 x602 y143)) ) ) ) )
                  ) )
          ||| ( y140 === var x466
              &&& ( y142 === ltrue () &&& (y143 === !!true)
                  &&& ( y141 === !!false &&& (y144 === !!false) &&& _lookupoNotoLookupo y139 x466 y145 y146 y147
                      ||| (y141 === !!true &&& (y144 === !!true) &&& __lookupoNotoLookupo y139 x466 y145 y146 y147) )
                  ||| ( y142 === lfalse () &&& (y143 === !!false)
                      &&& ( y141 === !!false &&& (y144 === !!false) &&& _lookupoNotoLookupo y139 x466 y145 y146 y147
                          ||| (y141 === !!true &&& (y144 === !!false) &&& ___lookupoNotoLookupo y139 x466 y145 y146 y147) )
                      ||| ( y142 === var x610
                          &&& ( y141 === !!false &&& (y143 === !!false) &&& (y144 === !!false)
                              &&& lookupoLookupoNotoLookupo y139 x610 x466 y145 y146 y147
                              ||| ( y141 === !!false &&& (y143 === !!true) &&& (y144 === !!false)
                                  &&& ( y139
                                      === pair x610 !!true % x714
                                      &&& _____lookupoNotoLookupo x610 x714 x466 y145 y146 y147
                                      ||| (y139 === pair x712 x713 % x714 &&& (lookupoLookupoLookupo x714 x610 x712 x713 x466 y146 y147 &&& __noto y145)) )
                                  ||| ( y141 === !!true &&& (y143 === !!false) &&& (y144 === !!false)
                                      &&& ( y139
                                          === pair x610 !!false % x796
                                          &&& ( x796
                                              === pair x466 !!true % x804
                                              &&& (y145 === !!true &&& _________________lookupo x610 x466 x804 y146 y147)
                                              ||| ( x796
                                                  === pair x802 x803 % x804
                                                  &&& (___________lookupoLookupo x804 x466 x610 x802 x803 y146 y147 &&& __noto y145) ) )
                                          ||| (y139 === pair x794 x795 % x796 &&& (_lookupoLookupoLookupo x796 x610 x794 x795 x466 y146 y147 &&& __noto y145))
                                          )
                                      ||| ( y141 === !!true &&& (y143 === !!true) &&& (y144 === !!true)
                                          &&& _lookupoLookupoNotoLookupo y139 x610 x466 y145 y146 y147 ) ) ) )
                          ||| ( y142 === neg x609
                              &&& ( x609 === ltrue ()
                                  &&& ( y141 === !!false &&& (y143 === !!false) &&& (y144 === !!false) &&& notoLookupoNotoLookupo y139 x466 y145 y146 y147
                                      ||| (y141 === !!true &&& (y143 === !!false) &&& (y144 === !!false) &&& ___lookupoNotoLookupo y139 x466 y145 y146 y147) )
                                  ||| ( x609 === lfalse ()
                                      &&& ( y141 === !!false &&& (y143 === !!true) &&& (y144 === !!false) &&& _lookupoNotoLookupo y139 x466 y145 y146 y147
                                          ||| (y141 === !!true &&& (y143 === !!true) &&& (y144 === !!true) &&& _notoLookupoNotoLookupo y139 x466 y145 y146 y147)
                                          )
                                      ||| ( x609 === var x946
                                          &&& ( y141 === !!false &&& (y143 === !!false) &&& (y144 === !!false)
                                              &&& lookupoNotoLookupoNotoLookupo y139 x946 x613 x466 y145 y146 y147
                                              ||| ( y141 === !!false &&& (y143 === !!true) &&& (y144 === !!false)
                                                  &&& ( y139
                                                      === pair x946 !!false % x995
                                                      &&& ____lookupoNotoLookupo x946 x995 x466 y145 y146 y147
                                                      ||| ( y139
                                                          === pair x993 x994 % x995
                                                          &&& (lookupoNotoLookupoLookupo x995 x946 x613 x993 x994 x466 y146 y147 &&& __noto y145) ) )
                                                  ||| ( y141 === !!true &&& (y143 === !!false) &&& (y144 === !!false)
                                                      &&& ( y139
                                                          === pair x946 !!true % x1015
                                                          &&& ( x466 === x946 &&& ___notoLookupo y145 x946 x1015 y146 y147
                                                              ||| ( x1015
                                                                  === pair x466 !!true % x1025
                                                                  &&& (y145 === !!true &&& _____________________lookupo x946 x466 x1025 y146 y147)
                                                                  ||| ( x1015
                                                                      === pair x1023 x1024 % x1025
                                                                      &&& (_______________lookupoLookupo x1025 x466 x946 x1023 x1024 y146 y147 &&& __noto y145)
                                                                      ) ) )
                                                          ||| ( y139
                                                              === pair x1013 x1014 % x1015
                                                              &&& (_lookupoNotoLookupoLookupo x1015 x946 x613 x1013 x1014 x466 y146 y147 &&& __noto y145) ) )
                                                      ||| ( y141 === !!true &&& (y143 === !!true) &&& (y144 === !!true)
                                                          &&& _lookupoNotoLookupoNotoLookupo y139 x946 x613 x466 y145 y146 y147 ) ) ) )
                                          ||| ( x609 === neg x945
                                              &&& ( logintoNotoNotoLookupoLookupo y139 x945 x949 x613 y143 x466 y141 y146 y147
                                                  &&& __andoNoto y141 y143 y144 y145 )
                                              ||| ( x609 === conj x1252 x1254
                                                  &&& ( __andoNoto y141 y143 y144 y145
                                                      &&& ( x1261 === x466
                                                          &&& logintoLogintoAndoNotoLookupo y139 x1252 x1256 x1254 x1257 x1259 y143 x1261 y141
                                                          &&& _lookupo y139 y146 y147 ) )
                                                  ||| ( x609 === disj x947 x948
                                                      &&& ( logintoLogintoOroNotoLookupoLookupo y139 x947 x949 x948 x950 x613 y143 x466 y141 y146 y147
                                                          &&& __andoNoto y141 y143 y144 y145 ) ) ) ) ) ) )
                              ||| ( y142 === conj x2788 x2790
                                  &&& ( logintoLogintoAndoLookupo y139 x2788 x2792 x2790 x2793 y143 y146 y147
                                      &&& (_noto y144 y145 &&& andoLookupo y141 y143 y144 y139 x466) )
                                  ||| ( y142 === disj x2807 x2809
                                      &&& ( logintoLogintoLookupo y139 x2807 x2808 x2809 x2810 y146 y147
                                          &&& (__andoNoto y141 y143 y144 y145 &&& (oro x2808 x2810 y143 &&& _lookupo y139 x466 y141)) ) ) ) ) ) ) )
              ||| ( y140 === neg x465 &&& _noto x469 y141
                  ||| ( y140 === conj x2872 x2874
                      &&& (logintoLogintoAndoLookupo y139 x2872 x2876 x2874 x2877 y141 y146 y147 &&& (_noto y144 y145 &&& logintoAndo y139 y142 y143 y141 y144))
                      ||| (y140 === disj x467 x468 &&& (oro x469 x470 y141 &&& _loginto y139 y142 y143)) ) ) ) ) )
  and _lookupoNotoLookupo y148 y149 y150 y151 y152 =
    fresh (x485 x484 x486)
      ( y148
      === pair y149 !!false % x486
      &&& _____notoLookupo y150 y149 x486 y151 y152
      ||| (y148 === pair x484 x485 % x486 &&& (___lookupoLookupo x486 y149 x484 x485 y151 y152 &&& __noto y150)) )
  and _____notoLookupo y153 y154 y155 y156 y157 = y153 === !!true &&& ______lookupo y154 y155 y156 y157
  and ___lookupoLookupo y158 y159 y160 y161 y162 y163 =
    fresh (x502 x501 x492 x491 x493)
      ( y158
      === pair y159 !!false % x493
      &&& ________lookupo y160 y161 y159 x493 y162 y163
      ||| ( y158
          === pair x491 x492 % x501
          &&& (x502 === pair x491 x492 % x501 &&& __lookupo x501 y159 &&& (x502 === pair x491 x492 % x501 &&& _______lookupo y160 y161 x502 y162 y163)) ) )
  and ________lookupo y164 y165 y166 y167 y168 y169 = y168 === y164 &&& (y169 === y165) ||| ______lookupo y166 y167 y168 y169
  and __lookupoNotoLookupo y170 y171 y172 y173 y174 =
    fresh (x508 x507 x509)
      ( y170
      === pair y171 !!true % x509
      &&& ______notoLookupo y172 y171 x509 y173 y174
      ||| (y170 === pair x507 x508 % x509 &&& (____lookupoLookupo x509 y171 x507 x508 y173 y174 &&& ___noto y172)) )
  and ______notoLookupo y175 y176 y177 y178 y179 = y175 === !!false &&& _____lookupo y176 y177 y178 y179
  and ____lookupoLookupo y180 y181 y182 y183 y184 y185 =
    fresh (x525 x524 x515 x514 x516)
      ( y180
      === pair y181 !!true % x516
      &&& _________lookupo y182 y183 y181 x516 y184 y185
      ||| ( y180
          === pair x514 x515 % x524
          &&& (x525 === pair x514 x515 % x524 &&& lookupo x524 y181 &&& (x525 === pair x514 x515 % x524 &&& _______lookupo y182 y183 x525 y184 y185)) ) )
  and _________lookupo y186 y187 y188 y189 y190 y191 = y190 === y186 &&& (y191 === y187) ||| _____lookupo y188 y189 y190 y191
  and andoNoto y192 y193 y194 = y192 === !!false &&& (y193 === !!false) &&& __noto y194 ||| (y192 === !!true &&& (y193 === !!true) &&& ___noto y194)
  and ___ando y195 y196 = y195 === !!false &&& (y196 === !!false) ||| (y195 === !!true &&& (y196 === !!true))
  and ___lookupoNotoLookupo y197 y198 y199 y200 y201 =
    fresh (x573 x572 x574)
      ( y197
      === pair y198 !!true % x574
      &&& ___notoLookupo y199 y198 x574 y200 y201
      ||| (y197 === pair x572 x573 % x574 &&& (____lookupoLookupo x574 y198 x572 x573 y200 y201 &&& __noto y199)) )
  and _andoNoto y202 y203 y204 = y202 === !!false &&& (y203 === !!false) &&& __noto y204 ||| (y202 === !!true &&& (y203 === !!false) &&& __noto y204)
  and ____ando y205 y206 = y205 === !!false &&& (y206 === !!false) ||| (y205 === !!true &&& (y206 === !!false))
  and lookupoLookupoNotoLookupo y207 y208 y209 y210 y211 y212 =
    fresh (x697 x696 x695 x667 x666 x668 x624 x623 x625)
      ( y207
      === pair y208 !!false % x625
      &&& ____lookupoNotoLookupo y208 x625 y209 y210 y211 y212
      ||| ( y207
          === pair x623 x624 % x625
          &&& ( x625
              === pair y208 !!false % x668
              &&& ______lookupoLookupo x623 x624 y208 x668 y209 y211 y212
              ||| ( x625
                  === pair x666 x667 % x695
                  &&& ( x696
                      === pair x666 x667 % x695
                      &&& (x697 === pair x666 x667 % x695)
                      &&& __lookupo x695 y208
                      &&& (x696 === pair x666 x667 % x695 &&& (x697 === pair x666 x667 % x695) &&& _______lookupoLookupo x623 x624 x696 y209 x697 y211 y212) )
                  )
              &&& __noto y210 ) ) )
  and ____lookupoNotoLookupo y213 y214 y215 y216 y217 y218 =
    fresh (x633 x632 x634)
      ( y215 === y213 &&& _____notoLookupo y216 y213 y214 y217 y218
      ||| ( y214
          === pair y215 !!false % x634
          &&& (y216 === !!true &&& __________lookupo y213 y215 x634 y217 y218)
          ||| (y214 === pair x632 x633 % x634 &&& (_____lookupoLookupo x634 y215 y213 x632 x633 y217 y218 &&& __noto y216)) ) )
  and __________lookupo y219 y220 y221 y222 y223 = y222 === y219 &&& (y223 === !!false) ||| ______lookupo y220 y221 y222 y223
  and _____lookupoLookupo y224 y225 y226 y227 y228 y229 y230 =
    fresh (x655 x654 x645 x644 x646)
      ( y224
      === pair y225 !!false % x646
      &&& ___________lookupo y226 y227 y228 y225 x646 y229 y230
      ||| ( y224
          === pair x644 x645 % x654
          &&& ( x655
              === pair x644 x645 % x654
              &&& __lookupo x654 y225
              &&& (x655 === pair x644 x645 % x654 &&& ____________lookupo y226 y227 y228 x655 y229 y230) ) ) )
  and ___________lookupo y231 y232 y233 y234 y235 y236 y237 = y236 === y231 &&& (y237 === !!false) ||| ________lookupo y232 y233 y234 y235 y236 y237
  and ____________lookupo y238 y239 y240 y241 y242 y243 = y242 === y238 &&& (y243 === !!false) ||| _______lookupo y239 y240 y241 y242 y243
  and ______lookupoLookupo y244 y245 y246 y247 y248 y249 y250 =
    fresh (x691 x690 x681 x680 x682)
      ( y248 === y244 &&& (y245 === !!false) &&& __________lookupo y244 y246 y247 y249 y250
      ||| ( y248 === y246 &&& ________lookupo y244 y245 y246 y247 y249 y250
          ||| ( y247
              === pair y248 !!false % x682
              &&& _____________lookupo y244 y245 y246 y248 x682 y249 y250
              ||| ( y247
                  === pair x680 x681 % x690
                  &&& ( x691
                      === pair x680 x681 % x690
                      &&& __lookupo x690 y248
                      &&& (x691 === pair x680 x681 % x690 &&& ________lookupo y244 y245 y246 x691 y249 y250) ) ) ) ) )
  and _____________lookupo y251 y252 y253 y254 y255 y256 y257 = y256 === y251 &&& (y257 === y252) ||| __________lookupo y253 y254 y255 y256 y257
  and _______lookupoLookupo y258 y259 y260 y261 y262 y263 y264 =
    y261 === y258 &&& (y259 === !!false) &&& ______lookupo y258 y262 y263 y264 ||| ________lookupoLookupo y260 y261 y258 y259 y262 y263 y264
  and ________lookupoLookupo y265 y266 y267 y268 y269 y270 y271 =
    fresh (x706 x705 x707)
      ( y265
      === pair y266 !!false % x707
      &&& _______lookupo y267 y268 y269 y270 y271
      ||| (y265 === pair x705 x706 % x707 &&& ________lookupoLookupo x707 y266 y267 y268 y269 y270 y271) )
  and _____lookupoNotoLookupo y272 y273 y274 y275 y276 y277 =
    fresh (x721 x720 x722)
      ( y273
      === pair y274 !!false % x722
      &&& (y275 === !!true &&& ______________lookupo y272 y274 x722 y276 y277)
      ||| (y273 === pair x720 x721 % x722 &&& (_________lookupoLookupo x722 y274 y272 x720 x721 y276 y277 &&& __noto y275)) )
  and ______________lookupo y278 y279 y280 y281 y282 = y281 === y278 &&& (y282 === !!true) ||| ______lookupo y279 y280 y281 y282
  and _________lookupoLookupo y283 y284 y285 y286 y287 y288 y289 =
    fresh (x743 x742 x733 x732 x734)
      ( y283
      === pair y284 !!false % x734
      &&& _______________lookupo y285 y286 y287 y284 x734 y288 y289
      ||| ( y283
          === pair x732 x733 % x742
          &&& ( x743
              === pair x732 x733 % x742
              &&& __lookupo x742 y284
              &&& (x743 === pair x732 x733 % x742 &&& ________________lookupo y285 y286 y287 x743 y288 y289) ) ) )
  and _______________lookupo y290 y291 y292 y293 y294 y295 y296 = y295 === y290 &&& (y296 === !!true) ||| ________lookupo y291 y292 y293 y294 y295 y296
  and ________________lookupo y297 y298 y299 y300 y301 y302 = y301 === y297 &&& (y302 === !!true) ||| _______lookupo y298 y299 y300 y301 y302
  and lookupoLookupoLookupo y303 y304 y305 y306 y307 y308 y309 =
    fresh (x789 x788 x787 x755 x754 x756)
      ( y303
      === pair y304 !!true % x756
      &&& __________lookupoLookupo y305 y306 y304 x756 y307 y308 y309
      ||| ( y303
          === pair x754 x755 % x787
          &&& ( x788
              === pair x754 x755 % x787
              &&& (x789 === pair x754 x755 % x787)
              &&& lookupo x787 y304
              &&& (x788 === pair x754 x755 % x787 &&& (x789 === pair x754 x755 % x787) &&& _______lookupoLookupo y305 y306 x788 y307 x789 y308 y309) ) ) )
  and __________lookupoLookupo y310 y311 y312 y313 y314 y315 y316 =
    fresh (x783 x782 x773 x772 x774)
      ( y314 === y310 &&& (y311 === !!false) &&& _________________lookupo y310 y312 y313 y315 y316
      ||| ( y313
          === pair y314 !!false % x774
          &&& __________________lookupo y310 y311 y312 y314 x774 y315 y316
          ||| ( y313
              === pair x772 x773 % x782
              &&& ( x783
                  === pair x772 x773 % x782
                  &&& __lookupo x782 y314
                  &&& (x783 === pair x772 x773 % x782 &&& _________lookupo y310 y311 y312 x783 y315 y316) ) ) ) )
  and _________________lookupo y317 y318 y319 y320 y321 = y320 === y317 &&& (y321 === !!false) ||| _____lookupo y318 y319 y320 y321
  and __________________lookupo y322 y323 y324 y325 y326 y327 y328 = y327 === y322 &&& (y328 === y323) ||| ______________lookupo y324 y325 y326 y327 y328
  and ___________lookupoLookupo y329 y330 y331 y332 y333 y334 y335 =
    fresh (x820 x819 x810 x809 x811)
      ( y329
      === pair y330 !!true % x811
      &&& ___________________lookupo y331 y332 y333 y330 x811 y334 y335
      ||| ( y329
          === pair x809 x810 % x819
          &&& (x820 === pair x809 x810 % x819 &&& lookupo x819 y330 &&& (x820 === pair x809 x810 % x819 &&& ____________lookupo y331 y332 y333 x820 y334 y335))
          ) )
  and ___________________lookupo y336 y337 y338 y339 y340 y341 y342 = y341 === y336 &&& (y342 === !!false) ||| _________lookupo y337 y338 y339 y340 y341 y342
  and _lookupoLookupoLookupo y343 y344 y345 y346 y347 y348 y349 =
    fresh (x856 x855 x854 x827 x826 x828)
      ( y343
      === pair y344 !!false % x828
      &&& ____________lookupoLookupo y345 y346 y344 x828 y347 y348 y349
      ||| ( y343
          === pair x826 x827 % x854
          &&& ( x855
              === pair x826 x827 % x854
              &&& (x856 === pair x826 x827 % x854)
              &&& __lookupo x854 y344
              &&& (x855 === pair x826 x827 % x854 &&& (x856 === pair x826 x827 % x854) &&& _____________lookupoLookupo y345 y346 x855 y347 x856 y348 y349) ) )
      )
  and ____________lookupoLookupo y350 y351 y352 y353 y354 y355 y356 =
    fresh (x850 x849 x840 x839 x841)
      ( y354 === y350 &&& (y351 === !!true) &&& ______________lookupo y350 y352 y353 y355 y356
      ||| ( y353
          === pair y354 !!true % x841
          &&& ____________________lookupo y350 y351 y352 y354 x841 y355 y356
          ||| ( y353
              === pair x839 x840 % x849
              &&& (x850 === pair x839 x840 % x849 &&& lookupo x849 y354 &&& (x850 === pair x839 x840 % x849 &&& ________lookupo y350 y351 y352 x850 y355 y356))
              ) ) )
  and ____________________lookupo y357 y358 y359 y360 y361 y362 y363 = y362 === y357 &&& (y363 === y358) ||| _________________lookupo y359 y360 y361 y362 y363
  and _____________lookupoLookupo y364 y365 y366 y367 y368 y369 y370 =
    y367 === y364 &&& (y365 === !!true) &&& _____lookupo y364 y368 y369 y370 ||| ______________lookupoLookupo y366 y367 y364 y365 y368 y369 y370
  and ______________lookupoLookupo y371 y372 y373 y374 y375 y376 y377 =
    fresh (x865 x864 x866)
      ( y371
      === pair y372 !!true % x866
      &&& _______lookupo y373 y374 y375 y376 y377
      ||| (y371 === pair x864 x865 % x866 &&& ______________lookupoLookupo x866 y372 y373 y374 y375 y376 y377) )
  and _lookupoLookupoNotoLookupo y378 y379 y380 y381 y382 y383 =
    fresh (x940 x939 x938 x910 x909 x911 x872 x871 x873)
      ( y378
      === pair y379 !!true % x873
      &&& ______lookupoNotoLookupo y379 x873 y380 y381 y382 y383
      ||| ( y378
          === pair x871 x872 % x873
          &&& ( x873
              === pair y379 !!true % x911
              &&& ________________lookupoLookupo x871 x872 y379 x911 y380 y382 y383
              ||| ( x873
                  === pair x909 x910 % x938
                  &&& ( x939
                      === pair x909 x910 % x938
                      &&& (x940 === pair x909 x910 % x938)
                      &&& lookupo x938 y379
                      &&& ( x939
                          === pair x909 x910 % x938
                          &&& (x940 === pair x909 x910 % x938)
                          &&& _____________lookupoLookupo x871 x872 x939 y380 x940 y382 y383 ) ) )
              &&& ___noto y381 ) ) )
  and ______lookupoNotoLookupo y384 y385 y386 y387 y388 y389 =
    fresh (x881 x880 x882)
      ( y386 === y384 &&& ______notoLookupo y387 y384 y385 y388 y389
      ||| ( y385
          === pair y386 !!true % x882
          &&& (y387 === !!false &&& _____________________lookupo y384 y386 x882 y388 y389)
          ||| (y385 === pair x880 x881 % x882 &&& (_______________lookupoLookupo x882 y386 y384 x880 x881 y388 y389 &&& ___noto y387)) ) )
  and _____________________lookupo y390 y391 y392 y393 y394 = y393 === y390 &&& (y394 === !!true) ||| _____lookupo y391 y392 y393 y394
  and _______________lookupoLookupo y395 y396 y397 y398 y399 y400 y401 =
    fresh (x903 x902 x893 x892 x894)
      ( y395
      === pair y396 !!true % x894
      &&& ______________________lookupo y397 y398 y399 y396 x894 y400 y401
      ||| ( y395
          === pair x892 x893 % x902
          &&& ( x903
              === pair x892 x893 % x902
              &&& lookupo x902 y396
              &&& (x903 === pair x892 x893 % x902 &&& ________________lookupo y397 y398 y399 x903 y400 y401) ) ) )
  and ______________________lookupo y402 y403 y404 y405 y406 y407 y408 = y407 === y402 &&& (y408 === !!true) ||| _________lookupo y403 y404 y405 y406 y407 y408
  and ________________lookupoLookupo y409 y410 y411 y412 y413 y414 y415 =
    fresh (x934 x933 x924 x923 x925)
      ( y413 === y409 &&& (y410 === !!true) &&& _____________________lookupo y409 y411 y412 y414 y415
      ||| ( y413 === y411 &&& _________lookupo y409 y410 y411 y412 y414 y415
          ||| ( y412
              === pair y413 !!true % x925
              &&& _______________________lookupo y409 y410 y411 y413 x925 y414 y415
              ||| ( y412
                  === pair x923 x924 % x933
                  &&& ( x934
                      === pair x923 x924 % x933
                      &&& lookupo x933 y413
                      &&& (x934 === pair x923 x924 % x933 &&& _________lookupo y409 y410 y411 x934 y414 y415) ) ) ) ) )
  and _______________________lookupo y416 y417 y418 y419 y420 y421 y422 =
    y421 === y416 &&& (y422 === y417) ||| _____________________lookupo y418 y419 y420 y421 y422
  and notoLookupoNotoLookupo y423 y424 y425 y426 y427 = _lookupoNotoLookupo y423 y424 y425 y426 y427
  and _notoLookupoNotoLookupo y428 y429 y430 y431 y432 = __lookupoNotoLookupo y428 y429 y430 y431 y432
  and lookupoNotoLookupoNotoLookupo y433 y434 y435 y436 y437 y438 y439 =
    fresh (x982 x981 x980 x975 x974 x976 x968 x967 x969)
      ( y433
      === pair y434 y435 % x969
      &&& (y435 === !!true &&& _____lookupoNotoLookupo y434 x969 y436 y437 y438 y439)
      ||| ( y433
          === pair x967 x968 % x969
          &&& ( x969
              === pair y434 y435 % x976
              &&& (y435 === !!true &&& __________lookupoLookupo x967 x968 y434 x976 y436 y438 y439)
              ||| ( x969
                  === pair x974 x975 % x980
                  &&& ( x981
                      === pair x974 x975 % x980
                      &&& (x982 === pair x974 x975 % x980)
                      &&& _lookupoNoto x980 y434 y435
                      &&& (x981 === pair x974 x975 % x980 &&& (x982 === pair x974 x975 % x980) &&& _______lookupoLookupo x967 x968 x981 y436 x982 y438 y439) )
                  )
              &&& __noto y437 ) ) )
  and _lookupoNoto y440 y441 y442 =
    fresh (x985 x984 x986) (y440 === pair y441 y442 % x986 &&& (y442 === !!true) ||| (y440 === pair x984 x985 % x986 &&& _lookupoNoto x986 y441 y442))
  and lookupoNotoLookupoLookupo y443 y444 y445 y446 y447 y448 y449 y450 =
    fresh (x1008 x1007 x1006 x1001 x1000 x1002)
      ( y443
      === pair y444 y445 % x1002
      &&& (y445 === !!false &&& ______lookupoLookupo y446 y447 y444 x1002 y448 y449 y450)
      ||| ( y443
          === pair x1000 x1001 % x1006
          &&& ( x1007
              === pair x1000 x1001 % x1006
              &&& (x1008 === pair x1000 x1001 % x1006)
              &&& lookupoNoto x1006 y444 y445
              &&& (x1007 === pair x1000 x1001 % x1006 &&& (x1008 === pair x1000 x1001 % x1006) &&& _______lookupoLookupo y446 y447 x1007 y448 x1008 y449 y450)
              ) ) )
  and _lookupoNotoLookupoLookupo y451 y452 y453 y454 y455 y456 y457 y458 =
    fresh (x1041 x1040 x1039 x1034 x1033 x1035)
      ( y451
      === pair y452 y453 % x1035
      &&& (y453 === !!true &&& ________________lookupoLookupo y454 y455 y452 x1035 y456 y457 y458)
      ||| ( y451
          === pair x1033 x1034 % x1039
          &&& ( x1040
              === pair x1033 x1034 % x1039
              &&& (x1041 === pair x1033 x1034 % x1039)
              &&& _lookupoNoto x1039 y452 y453
              &&& ( x1040
                  === pair x1033 x1034 % x1039
                  &&& (x1041 === pair x1033 x1034 % x1039)
                  &&& _____________lookupoLookupo y454 y455 x1040 y456 x1041 y457 y458 ) ) ) )
  and _lookupoNotoLookupoNotoLookupo y459 y460 y461 y462 y463 y464 y465 =
    fresh
      (x1073 x1072 x1071 x1066 x1065 x1067 x1047 x1046 x1048)
      ( y459
      === pair y460 y461 % x1048
      &&& (y461 === !!false &&& _______lookupoNotoLookupo y460 x1048 y462 y463 y464 y465)
      ||| ( y459
          === pair x1046 x1047 % x1048
          &&& ( x1048
              === pair y460 y461 % x1067
              &&& (y461 === !!false &&& ____________lookupoLookupo x1046 x1047 y460 x1067 y462 y464 y465)
              ||| ( x1048
                  === pair x1065 x1066 % x1071
                  &&& ( x1072
                      === pair x1065 x1066 % x1071
                      &&& (x1073 === pair x1065 x1066 % x1071)
                      &&& lookupoNoto x1071 y460 y461
                      &&& ( x1072
                          === pair x1065 x1066 % x1071
                          &&& (x1073 === pair x1065 x1066 % x1071)
                          &&& _____________lookupoLookupo x1046 x1047 x1072 y462 x1073 y464 y465 ) ) )
              &&& ___noto y463 ) ) )
  and _______lookupoNotoLookupo y466 y467 y468 y469 y470 y471 =
    fresh (x1056 x1055 x1057)
      ( y467
      === pair y468 !!true % x1057
      &&& (y469 === !!false &&& _________________lookupo y466 y468 x1057 y470 y471)
      ||| (y467 === pair x1055 x1056 % x1057 &&& (___________lookupoLookupo x1057 y468 y466 x1055 x1056 y470 y471 &&& ___noto y469)) )
  and logintoNotoNotoLookupoLookupo y472 y473 y474 y475 y476 y477 y478 y479 y480 =
    fresh
      (x1084 x1196 x1082 x1195 x1156 x1155 x1153 x1151 x1138 x1136 x1131 x1130 x1129 x1093 x1092 x1094 x1080)
      ( y473 === ltrue () &&& (y474 === !!true)
      &&& (y475 === !!false &&& notoLookupoLookupo y476 y472 y477 y478 y479 y480)
      ||| ( y473 === lfalse () &&& (y474 === !!false)
          &&& (y475 === !!true &&& _notoLookupoLookupo y476 y472 y477 y478 y479 y480)
          ||| ( y473 === var x1080
              &&& ( y472
                  === pair x1080 y474 % x1094
                  &&& ( y474 === !!true &&& (y475 === !!false)
                      &&& __notoLookupoLookupo y476 x1080 x1094 y477 y478 y479 y480
                      ||| (y474 === !!false &&& (y475 === !!true) &&& ___notoLookupoLookupo y476 x1080 x1094 y477 y478 y479 y480) )
                  ||| ( y472
                      === pair x1092 x1093 % x1129
                      &&& ( x1130
                          === pair x1092 x1093 % x1129
                          &&& (x1131 === pair x1092 x1093 % x1129)
                          &&& lookupoNotoNoto x1129 x1080 y474 y475 y476
                          &&& ( x1130
                              === pair x1092 x1093 % x1129
                              &&& (x1131 === pair x1092 x1093 % x1129)
                              &&& _lookupo x1130 y477 y478
                              &&& (x1130 === pair x1092 x1093 % x1129 &&& (x1131 === pair x1092 x1093 % x1129) &&& _lookupo x1131 y479 y480) ) ) ) )
              ||| ( y473 === neg x1136
                  &&& (logintoNotoNotoLookupoLookupo y472 x1136 x1138 y474 y475 y477 y478 y479 y480 &&& _noto y475 y476)
                  ||| ( y473 === conj x1151 x1153
                      &&& (logintoLogintoAndoNotoLookupo y472 x1151 x1155 x1153 x1156 y474 y475 y477 y478 &&& (_noto y475 y476 &&& _lookupo y472 y479 y480))
                      ||| ( y473 === disj x1195 x1082
                          &&& ( logintoLookupoLookupo y472 x1195 x1196 y477 y478 y479 y480
                              &&& (notoNoto y474 y475 y476 &&& logintoOro y472 x1082 x1084 x1196 y474) ) ) ) ) ) ) )
  and notoLookupoLookupo y481 y482 y483 y484 y485 y486 = y481 === !!true &&& _lookupoLookupo y482 y483 y484 y485 y486
  and _notoLookupoLookupo y487 y488 y489 y490 y491 y492 = y487 === !!false &&& _lookupoLookupo y488 y489 y490 y491 y492
  and __notoLookupoLookupo y493 y494 y495 y496 y497 y498 y499 = y493 === !!true &&& _________________lookupoLookupo y494 y495 y496 y497 y498 y499
  and _________________lookupoLookupo y500 y501 y502 y503 y504 y505 =
    fresh (x1104 x1103 x1105)
      ( y502 === y500 &&& (y503 === !!true) &&& _____lookupo y500 y501 y504 y505
      ||| ( y501
          === pair y502 y503 % x1105
          &&& ________________lookupo y500 y502 y503 x1105 y504 y505
          ||| (y501 === pair x1103 x1104 % x1105 &&& __________________lookupoLookupo x1105 y502 y503 y500 x1103 x1104 y504 y505) ) )
  and __________________lookupoLookupo y506 y507 y508 y509 y510 y511 y512 y513 =
    fresh (x1109) (x1109 === pair y510 y511 % y506 &&& _lookupo y506 y507 y508 &&& (x1109 === pair y510 y511 % y506 &&& _____lookupo y509 x1109 y512 y513))
  and ___notoLookupoLookupo y514 y515 y516 y517 y518 y519 y520 = y514 === !!false &&& ___________________lookupoLookupo y515 y516 y517 y518 y519 y520
  and ___________________lookupoLookupo y521 y522 y523 y524 y525 y526 =
    fresh (x1120 x1119 x1121)
      ( y523 === y521 &&& (y524 === !!false) &&& ______lookupo y521 y522 y525 y526
      ||| ( y522
          === pair y523 y524 % x1121
          &&& ____________lookupo y521 y523 y524 x1121 y525 y526
          ||| (y522 === pair x1119 x1120 % x1121 &&& ____________________lookupoLookupo x1121 y523 y524 y521 x1119 x1120 y525 y526) ) )
  and ____________________lookupoLookupo y527 y528 y529 y530 y531 y532 y533 y534 =
    fresh (x1125) (x1125 === pair y531 y532 % y527 &&& _lookupo y527 y528 y529 &&& (x1125 === pair y531 y532 % y527 &&& ______lookupo y530 x1125 y533 y534))
  and logintoLookupoLookupo y535 y536 y537 y538 y539 y540 y541 =
    fresh (x1205 x1203 x1202 x1204 x1200 x1201)
      ( y536 === ltrue () &&& (y537 === !!true) &&& _lookupoLookupo y535 y538 y539 y540 y541
      ||| ( y536 === lfalse () &&& (y537 === !!false) &&& _lookupoLookupo y535 y538 y539 y540 y541
          ||| ( y536 === var x1201
              &&& __lookupoLookupoLookupo y535 x1201 y537 y538 y539 y540 y541
              ||| ( y536 === neg x1200
                  &&& logintoNotoLookupoLookupo y535 x1200 x1204 y537 y538 y539 y540 y541
                  ||| ( y536 === conj x1202 x1203
                      &&& logintoLogintoAndoLookupoLookupo y535 x1202 x1204 x1203 x1205 y537 y538 y539 y540 y541
                      ||| (y536 === disj x1202 x1203 &&& logintoLogintoOroLookupoLookupo y535 x1202 x1204 x1203 x1205 y537 y538 y539 y540 y541) ) ) ) ) )
  and __lookupoLookupoLookupo y542 y543 y544 y545 y546 y547 y548 =
    fresh (x1221 x1220 x1219 x1210 x1209 x1211)
      ( y542
      === pair y543 y544 % x1211
      &&& (y545 === y543 &&& (y546 === y544) &&& _______lookupo y543 y544 x1211 y547 y548 ||| __lookupoLookupo x1211 y545 y546 y543 y544 y547 y548)
      ||| ( y542
          === pair x1209 x1210 % x1219
          &&& ( x1220
              === pair x1209 x1210 % x1219
              &&& (x1221 === pair x1209 x1210 % x1219)
              &&& _lookupo x1219 y543 y544
              &&& ( x1220
                  === pair x1209 x1210 % x1219
                  &&& (x1221 === pair x1209 x1210 % x1219)
                  &&& _lookupo x1220 y545 y546
                  &&& (x1220 === pair x1209 x1210 % x1219 &&& (x1221 === pair x1209 x1210 % x1219) &&& _lookupo x1221 y547 y548) ) ) ) )
  and logintoNotoLookupoLookupo y549 y550 y551 y552 y553 y554 y555 y556 = logintoLookupoLookupo y549 y550 y551 y553 y554 y555 y556 &&& _noto y551 y552
  and logintoLogintoAndoLookupoLookupo y557 y558 y559 y560 y561 y562 y563 y564 y565 y566 =
    logintoLookupoLookupo y557 y558 y559 y563 y564 y565 y566 &&& logintoAndo y557 y560 y561 y559 y562
  and logintoLogintoOroLookupoLookupo y567 y568 y569 y570 y571 y572 y573 y574 y575 y576 =
    logintoLookupoLookupo y567 y568 y569 y573 y574 y575 y576 &&& logintoOro y567 y570 y571 y569 y572
  and __andoNoto y577 y578 y579 y580 =
    y577 === !!false &&& (y578 === !!false) &&& (y579 === !!false) &&& __noto y580
    ||| ( y577 === !!false &&& (y578 === !!true) &&& (y579 === !!false) &&& __noto y580
        ||| ( y577 === !!true &&& (y578 === !!false) &&& (y579 === !!false) &&& __noto y580
            ||| (y577 === !!true &&& (y578 === !!true) &&& (y579 === !!true) &&& ___noto y580) ) )
  and logintoLogintoOroNotoLookupoLookupo y581 y582 y583 y584 y585 y586 y587 y588 y589 y590 y591 =
    fresh
      (x2773 x2772 x2770 x2768 x2700 x2699 x2697 x2695 x1281 x1277 x2675 x2674 x2672 x2670 x2637 x2636 x2634 x2632 x2602 x2600 x2599 x2604 x2597 x2595 x2567
         x2565 x2564 x2569 x2562 x2560 x2195 x2191 x2281 x2280 x2282 x2247 x2246 x2257 x2256 x2258 x2248 x1509 x2192 x1505 x1910 x1909 x1911 x1714 x1713 x1722
         x1721 x1723 x1715 x1506 x1278 x1499 x1498 x1496 x1494 x1472 x1471 x1469 x1467 x1460 x1459 x1438 x1431 x1430 x1428 x1426 x1404 x1403 x1401 x1399 x1392
         x1391 x1285)
      ( y582 === ltrue () &&& (y583 === !!true)
      &&& ( y584 === ltrue () &&& (y585 === !!true)
          &&& (y586 === !!true &&& _notoLookupoLookupo y587 y581 y588 y589 y590 y591)
          ||| ( y584 === lfalse () &&& (y585 === !!false)
              &&& (y586 === !!true &&& _notoLookupoLookupo y587 y581 y588 y589 y590 y591)
              ||| ( y584 === var x1285
                  &&& ( y585 === !!false &&& (y586 === !!true)
                      &&& __lookupoNotoLookupoLookupo y581 x1285 y587 y588 y589 y590 y591
                      ||| (y585 === !!true &&& (y586 === !!true) &&& ___lookupoNotoLookupoLookupo y581 x1285 y587 y588 y589 y590 y591) )
                  ||| ( y584 === neg x1391
                      &&& (logintoLookupoLookupo y581 x1391 x1392 y588 y589 y590 y591 &&& (oroNoto y585 y586 y587 &&& _noto x1392 y585))
                      ||| ( y584 === conj x1399 x1401
                          &&& ( logintoLogintoAndoLookupo y581 x1399 x1403 x1401 x1404 y585 y588 y589
                              &&& (_noto y586 y587 &&& (_oro y585 y586 &&& _lookupo y581 y590 y591)) )
                          ||| ( y584 === disj x1426 x1428
                              &&& ( logintoLogintoOroLookupoLookupo y581 x1426 x1430 x1428 x1431 y585 y588 y589 y590 y591
                                  &&& (_noto y586 y587 &&& _oro y585 y586) ) ) ) ) ) ) )
      ||| ( y582 === lfalse () &&& (y583 === !!false)
          &&& ( y584 === ltrue () &&& (y585 === !!true)
              &&& (y586 === !!true &&& _notoLookupoLookupo y587 y581 y588 y589 y590 y591)
              ||| ( y584 === lfalse () &&& (y585 === !!false)
                  &&& (y586 === !!false &&& notoLookupoLookupo y587 y581 y588 y589 y590 y591)
                  ||| ( y584 === var x1438
                      &&& ( y585 === !!false &&& (y586 === !!false)
                          &&& ____lookupoNotoLookupoLookupo y581 x1438 y587 y588 y589 y590 y591
                          ||| (y585 === !!true &&& (y586 === !!true) &&& ___lookupoNotoLookupoLookupo y581 x1438 y587 y588 y589 y590 y591) )
                      ||| ( y584 === neg x1459
                          &&& (logintoLookupoLookupo y581 x1459 x1460 y588 y589 y590 y591 &&& (_oroNoto y585 y586 y587 &&& _noto x1460 y585))
                          ||| ( y584 === conj x1467 x1469
                              &&& ( logintoLogintoAndoLookupo y581 x1467 x1471 x1469 x1472 y585 y588 y589
                                  &&& (_noto y586 y587 &&& (__oro y585 y586 &&& _lookupo y581 y590 y591)) )
                              ||| ( y584 === disj x1494 x1496
                                  &&& ( logintoLogintoOroLookupoLookupo y581 x1494 x1498 x1496 x1499 y585 y588 y589 y590 y591
                                      &&& (_noto y586 y587 &&& __oro y585 y586) ) ) ) ) ) ) )
          ||| ( y582 === var x1278
              &&& ( y584 === ltrue () &&& (y585 === !!true)
                  &&& ( y583 === !!false &&& (y586 === !!true)
                      &&& __lookupoNotoLookupoLookupo y581 x1278 y587 y588 y589 y590 y591
                      ||| (y583 === !!true &&& (y586 === !!true) &&& ___lookupoNotoLookupoLookupo y581 x1278 y587 y588 y589 y590 y591) )
                  ||| ( y584 === lfalse () &&& (y585 === !!false)
                      &&& ( y583 === !!false &&& (y586 === !!false)
                          &&& ____lookupoNotoLookupoLookupo y581 x1278 y587 y588 y589 y590 y591
                          ||| (y583 === !!true &&& (y586 === !!true) &&& ___lookupoNotoLookupoLookupo y581 x1278 y587 y588 y589 y590 y591) )
                      ||| ( y584 === var x1506
                          &&& ( y583 === !!false &&& (y585 === !!false) &&& (y586 === !!false)
                              &&& lookupoLookupoNotoLookupoLookupo y581 x1506 x1278 y587 y588 y589 y590 y591
                              ||| ( y583 === !!false &&& (y585 === !!true) &&& (y586 === !!true)
                                  &&& ( y581
                                      === pair x1506 !!true % x1715
                                      &&& ( x1715
                                          === pair x1278 !!false % x1723
                                          &&& (y587 === !!false &&& ________________________________lookupoLookupo x1506 x1278 x1723 y588 y589 y590 y591)
                                          ||| ( x1715
                                              === pair x1721 x1722 % x1723
                                              &&& (_________lookupoLookupoLookupo x1723 x1278 x1506 x1721 x1722 y588 y589 y590 y591 &&& ___noto y587) ) )
                                      ||| ( y581
                                          === pair x1713 x1714 % x1715
                                          &&& (lookupoLookupoLookupoLookupo x1715 x1506 x1713 x1714 x1278 y588 y589 y590 y591 &&& ___noto y587) ) )
                                  ||| ( y583 === !!true &&& (y585 === !!false) &&& (y586 === !!true)
                                      &&& ( y581
                                          === pair x1506 !!false % x1911
                                          &&& ______lookupoNotoLookupoLookupo x1506 x1911 x1278 y587 y588 y589 y590 y591
                                          ||| ( y581
                                              === pair x1909 x1910 % x1911
                                              &&& (_lookupoLookupoLookupoLookupo x1911 x1506 x1909 x1910 x1278 y588 y589 y590 y591 &&& ___noto y587) ) )
                                      ||| ( y583 === !!true &&& (y585 === !!true) &&& (y586 === !!true)
                                          &&& _lookupoLookupoNotoLookupoLookupo y581 x1506 x1278 y587 y588 y589 y590 y591 ) ) ) )
                          ||| ( y584 === neg x1505
                              &&& ( x1505 === ltrue ()
                                  &&& ( y583 === !!false &&& (y585 === !!false) &&& (y586 === !!false)
                                      &&& notoLookupoNotoLookupoLookupo y581 x1278 y587 y588 y589 y590 y591
                                      ||| ( y583 === !!true &&& (y585 === !!false) &&& (y586 === !!true)
                                          &&& ___lookupoNotoLookupoLookupo y581 x1278 y587 y588 y589 y590 y591 ) )
                                  ||| ( x1505 === lfalse ()
                                      &&& ( y583 === !!false &&& (y585 === !!true) &&& (y586 === !!true)
                                          &&& __lookupoNotoLookupoLookupo y581 x1278 y587 y588 y589 y590 y591
                                          ||| ( y583 === !!true &&& (y585 === !!true) &&& (y586 === !!true)
                                              &&& _notoLookupoNotoLookupoLookupo y581 x1278 y587 y588 y589 y590 y591 ) )
                                      ||| ( x1505 === var x2192
                                          &&& ( y583 === !!false &&& (y585 === !!false) &&& (y586 === !!false)
                                              &&& lookupoNotoLookupoNotoLookupoLookupo y581 x2192 x1509 x1278 y587 y588 y589 y590 y591
                                              ||| ( y583 === !!false &&& (y585 === !!true) &&& (y586 === !!true)
                                                  &&& ( y581
                                                      === pair x2192 !!false % x2248
                                                      &&& ( x1278 === x2192
                                                          &&& ___notoLookupoLookupo y587 x2192 x2248 y588 y589 y590 y591
                                                          ||| ( x2248
                                                              === pair x1278 !!false % x2258
                                                              &&& ( y587 === !!false
                                                                  &&& _________________________lookupoLookupo x2192 x1278 x2258 y588 y589 y590 y591 )
                                                              ||| ( x2248
                                                                  === pair x2256 x2257 % x2258
                                                                  &&& ( _____lookupoLookupoLookupo x2258 x1278 x2192 x2256 x2257 y588 y589 y590 y591
                                                                      &&& ___noto y587 ) ) ) )
                                                      ||| ( y581
                                                          === pair x2246 x2247 % x2248
                                                          &&& ( lookupoNotoLookupoLookupoLookupo x2248 x2192 x1509 x2246 x2247 x1278 y588 y589 y590 y591
                                                              &&& ___noto y587 ) ) )
                                                  ||| ( y583 === !!true &&& (y585 === !!false) &&& (y586 === !!true)
                                                      &&& ( y581
                                                          === pair x2192 !!true % x2282
                                                          &&& _______lookupoNotoLookupoLookupo x2192 x2282 x1278 y587 y588 y589 y590 y591
                                                          ||| ( y581
                                                              === pair x2280 x2281 % x2282
                                                              &&& ( _lookupoNotoLookupoLookupoLookupo x2282 x2192 x1509 x2280 x2281 x1278 y588 y589 y590 y591
                                                                  &&& ___noto y587 ) ) )
                                                      ||| ( y583 === !!true &&& (y585 === !!true) &&& (y586 === !!true)
                                                          &&& _lookupoNotoLookupoNotoLookupoLookupo y581 x2192 x1509 x1278 y587 y588 y589 y590 y591 ) ) ) )
                                          ||| ( x1505 === neg x2191
                                              &&& ( logintoNotoNotoLookupoLookupoLookupo y581 x2191 x2195 x1509 y585 x1278 y583 y588 y589 y590 y591
                                                  &&& __oroNoto y583 y585 y586 y587 )
                                              ||| ( x1505 === conj x2560 x2562
                                                  &&& ( __oroNoto y583 y585 y586 y587
                                                      &&& ( x2569 === x1278
                                                          &&& logintoLogintoAndoNotoLookupo y581 x2560 x2564 x2562 x2565 x2567 y585 x2569 y583
                                                          &&& _lookupoLookupo y581 y588 y589 y590 y591 ) )
                                                  ||| ( x1505 === disj x2595 x2597
                                                      &&& ( __oroNoto y583 y585 y586 y587
                                                          &&& ( x2604 === x1278
                                                              &&& logintoLogintoOroNotoLookupoLookupo y581 x2595 x2599 x2597 x2600 x2602 y585 x2604 y583 y588
                                                                    y589
                                                              &&& _lookupo y581 y590 y591 ) ) ) ) ) ) ) )
                              ||| ( y584 === conj x2632 x2634
                                  &&& ( logintoLogintoAndoLookupo y581 x2632 x2636 x2634 x2637 y585 y588 y589
                                      &&& ( _noto y586 y587
                                          &&& ( y583 === !!false &&& (y585 === !!false) &&& (y586 === !!false)
                                              &&& _________________________________________lookupoLookupo y581 x1278 y590 y591
                                              ||| ( y583 === !!false &&& (y585 === !!true) &&& (y586 === !!true)
                                                  &&& _________________________________________lookupoLookupo y581 x1278 y590 y591
                                                  ||| ( y583 === !!true &&& (y585 === !!false) &&& (y586 === !!true)
                                                      &&& __________________________________________lookupoLookupo y581 x1278 y590 y591
                                                      ||| ( y583 === !!true &&& (y585 === !!true) &&& (y586 === !!true)
                                                          &&& __________________________________________lookupoLookupo y581 x1278 y590 y591 ) ) ) ) ) )
                                  ||| ( y584 === disj x2670 x2672
                                      &&& ( logintoLogintoOroLookupoLookupo y581 x2670 x2674 x2672 x2675 y585 y588 y589 y590 y591
                                          &&& (_noto y586 y587 &&& oroLookupo y583 y585 y586 y581 x1278) ) ) ) ) ) ) )
              ||| ( y582 === neg x1277 &&& _noto x1281 y583
                  ||| ( y582 === conj x2695 x2697
                      &&& ( logintoLogintoAndoLookupo y581 x2695 x2699 x2697 x2700 y583 y588 y589
                          &&& (_noto y586 y587 &&& logintoOroLookupo y581 y584 y585 y583 y586 y590 y591) )
                      ||| ( y582 === disj x2768 x2770
                          &&& ( logintoLogintoOroLookupoLookupo y581 x2768 x2772 x2770 x2773 y583 y588 y589 y590 y591
                              &&& (_noto y586 y587 &&& logintoOro y581 y584 y585 y583 y586) ) ) ) ) ) ) )
  and __lookupoNotoLookupoLookupo y592 y593 y594 y595 y596 y597 y598 =
    fresh (x1297 x1296 x1298)
      ( y592
      === pair y593 !!false % x1298
      &&& ___notoLookupoLookupo y594 y593 x1298 y595 y596 y597 y598
      ||| (y592 === pair x1296 x1297 % x1298 &&& (___lookupoLookupoLookupo x1298 y593 x1296 x1297 y595 y596 y597 y598 &&& ___noto y594)) )
  and ___lookupoLookupoLookupo y599 y600 y601 y602 y603 y604 y605 y606 =
    fresh (x1333 x1332 x1331 x1303 x1302 x1304)
      ( y599
      === pair y600 !!false % x1304
      &&& _____________________lookupoLookupo y601 y602 y600 x1304 y603 y604 y605 y606
      ||| ( y599
          === pair x1302 x1303 % x1331
          &&& ( x1332
              === pair x1302 x1303 % x1331
              &&& (x1333 === pair x1302 x1303 % x1331)
              &&& __lookupo x1331 y600
              &&& ( x1332
                  === pair x1302 x1303 % x1331
                  &&& (x1333 === pair x1302 x1303 % x1331)
                  &&& ______________________lookupoLookupo y601 y602 x1332 y603 y604 x1333 y605 y606 ) ) ) )
  and _____________________lookupoLookupo y607 y608 y609 y610 y611 y612 y613 y614 =
    fresh (x1327 x1326 x1317 x1316 x1318)
      ( y611 === y607 &&& (y612 === y608) &&& ________lookupo y607 y608 y609 y610 y613 y614
      ||| ( y611 === y609 &&& (y612 === !!false) &&& ________lookupo y607 y608 y609 y610 y613 y614
          ||| ( y610
              === pair y611 y612 % x1318
              &&& ________________________lookupo y607 y608 y609 y611 y612 x1318 y613 y614
              ||| ( y610
                  === pair x1316 x1317 % x1326
                  &&& ( x1327
                      === pair x1316 x1317 % x1326
                      &&& _lookupo x1326 y611 y612
                      &&& (x1327 === pair x1316 x1317 % x1326 &&& ________lookupo y607 y608 y609 x1327 y613 y614) ) ) ) ) )
  and ________________________lookupo y615 y616 y617 y618 y619 y620 y621 y622 =
    y621 === y615 &&& (y622 === y616) ||| ____________lookupo y617 y618 y619 y620 y621 y622
  and ______________________lookupoLookupo y623 y624 y625 y626 y627 y628 y629 y630 =
    y626 === y623 &&& (y627 === y624) &&& _______lookupo y623 y624 y628 y629 y630
    ||| _______________________lookupoLookupo y625 y626 y627 y623 y624 y628 y629 y630
  and _______________________lookupoLookupo y631 y632 y633 y634 y635 y636 y637 y638 =
    fresh (x1342 x1341 x1343)
      ( y631
      === pair y632 y633 % x1343
      &&& _______lookupo y634 y635 y636 y637 y638
      ||| (y631 === pair x1341 x1342 % x1343 &&& _______________________lookupoLookupo x1343 y632 y633 y634 y635 y636 y637 y638) )
  and ___lookupoNotoLookupoLookupo y639 y640 y641 y642 y643 y644 y645 =
    fresh (x1349 x1348 x1350)
      ( y639
      === pair y640 !!true % x1350
      &&& ____notoLookupoLookupo y641 y640 x1350 y642 y643 y644 y645
      ||| (y639 === pair x1348 x1349 % x1350 &&& (____lookupoLookupoLookupo x1350 y640 x1348 x1349 y642 y643 y644 y645 &&& ___noto y641)) )
  and ____notoLookupoLookupo y646 y647 y648 y649 y650 y651 y652 = y646 === !!false &&& _________________lookupoLookupo y647 y648 y649 y650 y651 y652
  and ____lookupoLookupoLookupo y653 y654 y655 y656 y657 y658 y659 y660 =
    fresh (x1386 x1385 x1384 x1356 x1355 x1357)
      ( y653
      === pair y654 !!true % x1357
      &&& ________________________lookupoLookupo y655 y656 y654 x1357 y657 y658 y659 y660
      ||| ( y653
          === pair x1355 x1356 % x1384
          &&& ( x1385
              === pair x1355 x1356 % x1384
              &&& (x1386 === pair x1355 x1356 % x1384)
              &&& lookupo x1384 y654
              &&& ( x1385
                  === pair x1355 x1356 % x1384
                  &&& (x1386 === pair x1355 x1356 % x1384)
                  &&& ______________________lookupoLookupo y655 y656 x1385 y657 y658 x1386 y659 y660 ) ) ) )
  and ________________________lookupoLookupo y661 y662 y663 y664 y665 y666 y667 y668 =
    fresh (x1380 x1379 x1370 x1369 x1371)
      ( y665 === y661 &&& (y666 === y662) &&& _________lookupo y661 y662 y663 y664 y667 y668
      ||| ( y665 === y663 &&& (y666 === !!true) &&& _________lookupo y661 y662 y663 y664 y667 y668
          ||| ( y664
              === pair y665 y666 % x1371
              &&& _________________________lookupo y661 y662 y663 y665 y666 x1371 y667 y668
              ||| ( y664
                  === pair x1369 x1370 % x1379
                  &&& ( x1380
                      === pair x1369 x1370 % x1379
                      &&& _lookupo x1379 y665 y666
                      &&& (x1380 === pair x1369 x1370 % x1379 &&& _________lookupo y661 y662 y663 x1380 y667 y668) ) ) ) ) )
  and _________________________lookupo y669 y670 y671 y672 y673 y674 y675 y676 =
    y675 === y669 &&& (y676 === y670) ||| ________________lookupo y671 y672 y673 y674 y675 y676
  and oroNoto y677 y678 y679 = y677 === !!false &&& (y678 === !!true) &&& ___noto y679 ||| (y677 === !!true &&& (y678 === !!true) &&& ___noto y679)
  and _oro y680 y681 = y680 === !!false &&& (y681 === !!true) ||| (y680 === !!true &&& (y681 === !!true))
  and ____lookupoNotoLookupoLookupo y682 y683 y684 y685 y686 y687 y688 =
    fresh (x1450 x1449 x1451)
      ( y682
      === pair y683 !!false % x1451
      &&& _____notoLookupoLookupo y684 y683 x1451 y685 y686 y687 y688
      ||| (y682 === pair x1449 x1450 % x1451 &&& (___lookupoLookupoLookupo x1451 y683 x1449 x1450 y685 y686 y687 y688 &&& __noto y684)) )
  and _____notoLookupoLookupo y689 y690 y691 y692 y693 y694 y695 = y689 === !!true &&& ___________________lookupoLookupo y690 y691 y692 y693 y694 y695
  and _oroNoto y696 y697 y698 = y696 === !!false &&& (y697 === !!false) &&& __noto y698 ||| (y696 === !!true &&& (y697 === !!true) &&& ___noto y698)
  and __oro y699 y700 = y699 === !!false &&& (y700 === !!false) ||| (y699 === !!true &&& (y700 === !!true))
  and lookupoLookupoNotoLookupoLookupo y701 y702 y703 y704 y705 y706 y707 y708 =
    fresh
      (x1688 x1687 x1686 x1685 x1617 x1616 x1618 x1520 x1519 x1521)
      ( y701
      === pair y702 !!false % x1521
      &&& _____lookupoNotoLookupoLookupo y702 x1521 y703 y704 y705 y706 y707 y708
      ||| ( y701
          === pair x1519 x1520 % x1521
          &&& ( x1521
              === pair y702 !!false % x1618
              &&& ______lookupoLookupoLookupo x1519 x1520 y702 x1618 y703 y705 y706 y707 y708
              ||| ( x1521
                  === pair x1616 x1617 % x1685
                  &&& ( x1686
                      === pair x1616 x1617 % x1685
                      &&& (x1687 === pair x1616 x1617 % x1685)
                      &&& (x1688 === pair x1616 x1617 % x1685)
                      &&& __lookupo x1685 y702
                      &&& ( x1686
                          === pair x1616 x1617 % x1685
                          &&& (x1687 === pair x1616 x1617 % x1685)
                          &&& (x1688 === pair x1616 x1617 % x1685)
                          &&& _______lookupoLookupoLookupo x1519 x1520 x1686 y703 x1687 y705 y706 x1688 y707 y708 ) ) )
              &&& __noto y704 ) ) )
  and _____lookupoNotoLookupoLookupo y709 y710 y711 y712 y713 y714 y715 y716 =
    fresh (x1529 x1528 x1530)
      ( y711 === y709
      &&& _____notoLookupoLookupo y712 y709 y710 y713 y714 y715 y716
      ||| ( y710
          === pair y711 !!false % x1530
          &&& (y712 === !!true &&& _________________________lookupoLookupo y709 y711 x1530 y713 y714 y715 y716)
          ||| (y710 === pair x1528 x1529 % x1530 &&& (_____lookupoLookupoLookupo x1530 y711 y709 x1528 x1529 y713 y714 y715 y716 &&& __noto y712)) ) )
  and _________________________lookupoLookupo y717 y718 y719 y720 y721 y722 y723 =
    fresh (x1554 x1553 x1544 x1543 x1545)
      ( y720 === y717 &&& (y721 === !!false) &&& __________lookupo y717 y718 y719 y722 y723
      ||| ( y720 === y718 &&& (y721 === !!false) &&& __________lookupo y717 y718 y719 y722 y723
          ||| ( y719
              === pair y720 y721 % x1545
              &&& __________________________lookupo y717 y718 y720 y721 x1545 y722 y723
              ||| ( y719
                  === pair x1543 x1544 % x1553
                  &&& ( x1554
                      === pair x1543 x1544 % x1553
                      &&& _lookupo x1553 y720 y721
                      &&& (x1554 === pair x1543 x1544 % x1553 &&& __________lookupo y717 y718 x1554 y722 y723) ) ) ) ) )
  and __________________________lookupo y724 y725 y726 y727 y728 y729 y730 =
    y729 === y724 &&& (y730 === !!false) ||| ____________lookupo y725 y726 y727 y728 y729 y730
  and _____lookupoLookupoLookupo y731 y732 y733 y734 y735 y736 y737 y738 y739 =
    fresh
      (x1595 x1594 x1593 x1560 x1559 x1589 x1588 x1579 x1578 x1580 x1561)
      ( y731
      === pair y732 !!false % x1561
      &&& ( y736 === y733 &&& (y737 === !!false)
          &&& ___________lookupo y733 y734 y735 y732 x1561 y738 y739
          ||| ( y736 === y734 &&& (y737 === y735)
              &&& ___________lookupo y733 y734 y735 y732 x1561 y738 y739
              ||| ( y736 === y732 &&& (y737 === !!false)
                  &&& ___________lookupo y733 y734 y735 y732 x1561 y738 y739
                  ||| ( x1561
                      === pair y736 y737 % x1580
                      &&& (y738 === y733 &&& (y739 === !!false) ||| ________________________lookupo y734 y735 y732 y736 y737 x1580 y738 y739)
                      ||| ( x1561
                          === pair x1578 x1579 % x1588
                          &&& ( x1589
                              === pair x1578 x1579 % x1588
                              &&& _lookupo x1588 y736 y737
                              &&& (x1589 === pair x1578 x1579 % x1588 &&& ___________lookupo y733 y734 y735 y732 x1589 y738 y739) ) ) ) ) ) )
      ||| ( y731
          === pair x1559 x1560 % x1593
          &&& ( x1594
              === pair x1559 x1560 % x1593
              &&& (x1595 === pair x1559 x1560 % x1593)
              &&& __lookupo x1593 y732
              &&& ( x1594
                  === pair x1559 x1560 % x1593
                  &&& (x1595 === pair x1559 x1560 % x1593)
                  &&& __________________________lookupoLookupo y733 y734 y735 x1594 y736 y737 x1595 y738 y739 ) ) ) )
  and __________________________lookupoLookupo y740 y741 y742 y743 y744 y745 y746 y747 y748 =
    y744 === y740 &&& (y745 === !!false) &&& ____________lookupo y740 y741 y742 y746 y747 y748
    ||| ( y744 === y741 &&& (y745 === y742) &&& ____________lookupo y740 y741 y742 y746 y747 y748
        ||| ___________________________lookupoLookupo y743 y744 y745 y740 y741 y742 y746 y747 y748 )
  and ___________________________lookupoLookupo y749 y750 y751 y752 y753 y754 y755 y756 y757 =
    fresh (x1609 x1608 x1610)
      ( y749
      === pair y750 y751 % x1610
      &&& ____________lookupo y752 y753 y754 y755 y756 y757
      ||| (y749 === pair x1608 x1609 % x1610 &&& ___________________________lookupoLookupo x1610 y750 y751 y752 y753 y754 y755 y756 y757) )
  and ______lookupoLookupoLookupo y758 y759 y760 y761 y762 y763 y764 y765 y766 =
    fresh
      (x1666 x1665 x1664 x1631 x1630 x1660 x1659 x1650 x1649 x1651 x1632)
      ( y762 === y758 &&& (y759 === !!false)
      &&& _________________________lookupoLookupo y758 y760 y761 y763 y764 y765 y766
      ||| ( y762 === y760
          &&& _____________________lookupoLookupo y758 y759 y760 y761 y763 y764 y765 y766
          ||| ( y761
              === pair y762 !!false % x1632
              &&& ( y763 === y758 &&& (y764 === y759)
                  &&& _____________lookupo y758 y759 y760 y762 x1632 y765 y766
                  ||| ( y763 === y760 &&& (y764 === !!false)
                      &&& _____________lookupo y758 y759 y760 y762 x1632 y765 y766
                      ||| ( y763 === y762 &&& (y764 === !!false)
                          &&& _____________lookupo y758 y759 y760 y762 x1632 y765 y766
                          ||| ( x1632
                              === pair y763 y764 % x1651
                              &&& (y765 === y758 &&& (y766 === y759) ||| __________________________lookupo y760 y762 y763 y764 x1651 y765 y766)
                              ||| ( x1632
                                  === pair x1649 x1650 % x1659
                                  &&& ( x1660
                                      === pair x1649 x1650 % x1659
                                      &&& _lookupo x1659 y763 y764
                                      &&& (x1660 === pair x1649 x1650 % x1659 &&& _____________lookupo y758 y759 y760 y762 x1660 y765 y766) ) ) ) ) ) )
              ||| ( y761
                  === pair x1630 x1631 % x1664
                  &&& ( x1665
                      === pair x1630 x1631 % x1664
                      &&& (x1666 === pair x1630 x1631 % x1664)
                      &&& __lookupo x1664 y762
                      &&& ( x1665
                          === pair x1630 x1631 % x1664
                          &&& (x1666 === pair x1630 x1631 % x1664)
                          &&& ____________________________lookupoLookupo y758 y759 y760 x1665 y763 y764 x1666 y765 y766 ) ) ) ) ) )
  and ____________________________lookupoLookupo y767 y768 y769 y770 y771 y772 y773 y774 y775 =
    y771 === y767 &&& (y772 === y768) &&& ________lookupo y767 y768 y769 y773 y774 y775
    ||| ( y771 === y769 &&& (y772 === !!false) &&& ________lookupo y767 y768 y769 y773 y774 y775
        ||| _____________________________lookupoLookupo y770 y771 y772 y767 y768 y769 y773 y774 y775 )
  and _____________________________lookupoLookupo y776 y777 y778 y779 y780 y781 y782 y783 y784 =
    fresh (x1680 x1679 x1681)
      ( y776
      === pair y777 y778 % x1681
      &&& ________lookupo y779 y780 y781 y782 y783 y784
      ||| (y776 === pair x1679 x1680 % x1681 &&& _____________________________lookupoLookupo x1681 y777 y778 y779 y780 y781 y782 y783 y784) )
  and _______lookupoLookupoLookupo y785 y786 y787 y788 y789 y790 y791 y792 y793 y794 =
    y788 === y785 &&& (y786 === !!false)
    &&& ______________________________lookupoLookupo y785 y789 y790 y791 y792 y793 y794
    ||| ________lookupoLookupoLookupo y787 y788 y785 y786 y789 y790 y791 y792 y793 y794
  and ______________________________lookupoLookupo y795 y796 y797 y798 y799 y800 y801 =
    y797 === y795 &&& (y798 === !!false) &&& ______lookupo y795 y799 y800 y801
    ||| _______________________________lookupoLookupo y796 y797 y798 y795 y799 y800 y801
  and _______________________________lookupoLookupo y802 y803 y804 y805 y806 y807 y808 =
    fresh (x1701 x1700 x1702)
      ( y802
      === pair y803 y804 % x1702
      &&& ______lookupo y805 y806 y807 y808
      ||| (y802 === pair x1700 x1701 % x1702 &&& _______________________________lookupoLookupo x1702 y803 y804 y805 y806 y807 y808) )
  and ________lookupoLookupoLookupo y809 y810 y811 y812 y813 y814 y815 y816 y817 y818 =
    fresh (x1707 x1706 x1708)
      ( y809
      === pair y810 !!false % x1708
      &&& ______________________lookupoLookupo y811 y812 y813 y814 y815 y816 y817 y818
      ||| (y809 === pair x1706 x1707 % x1708 &&& ________lookupoLookupoLookupo x1708 y810 y811 y812 y813 y814 y815 y816 y817 y818) )
  and ________________________________lookupoLookupo y819 y820 y821 y822 y823 y824 y825 =
    fresh (x1747 x1746 x1737 x1736 x1738)
      ( y822 === y819 &&& (y823 === !!true) &&& ______________lookupo y819 y820 y821 y824 y825
      ||| ( y822 === y820 &&& (y823 === !!false) &&& ______________lookupo y819 y820 y821 y824 y825
          ||| ( y821
              === pair y822 y823 % x1738
              &&& ___________________________lookupo y819 y820 y822 y823 x1738 y824 y825
              ||| ( y821
                  === pair x1736 x1737 % x1746
                  &&& ( x1747
                      === pair x1736 x1737 % x1746
                      &&& _lookupo x1746 y822 y823
                      &&& (x1747 === pair x1736 x1737 % x1746 &&& ______________lookupo y819 y820 x1747 y824 y825) ) ) ) ) )
  and ___________________________lookupo y826 y827 y828 y829 y830 y831 y832 =
    y831 === y826 &&& (y832 === !!true) ||| ____________lookupo y827 y828 y829 y830 y831 y832
  and _________lookupoLookupoLookupo y833 y834 y835 y836 y837 y838 y839 y840 y841 =
    fresh
      (x1788 x1787 x1786 x1753 x1752 x1782 x1781 x1772 x1771 x1773 x1754)
      ( y833
      === pair y834 !!false % x1754
      &&& ( y838 === y835 &&& (y839 === !!true)
          &&& _______________lookupo y835 y836 y837 y834 x1754 y840 y841
          ||| ( y838 === y836 &&& (y839 === y837)
              &&& _______________lookupo y835 y836 y837 y834 x1754 y840 y841
              ||| ( y838 === y834 &&& (y839 === !!false)
                  &&& _______________lookupo y835 y836 y837 y834 x1754 y840 y841
                  ||| ( x1754
                      === pair y838 y839 % x1773
                      &&& (y840 === y835 &&& (y841 === !!true) ||| ________________________lookupo y836 y837 y834 y838 y839 x1773 y840 y841)
                      ||| ( x1754
                          === pair x1771 x1772 % x1781
                          &&& ( x1782
                              === pair x1771 x1772 % x1781
                              &&& _lookupo x1781 y838 y839
                              &&& (x1782 === pair x1771 x1772 % x1781 &&& _______________lookupo y835 y836 y837 y834 x1782 y840 y841) ) ) ) ) ) )
      ||| ( y833
          === pair x1752 x1753 % x1786
          &&& ( x1787
              === pair x1752 x1753 % x1786
              &&& (x1788 === pair x1752 x1753 % x1786)
              &&& __lookupo x1786 y834
              &&& ( x1787
                  === pair x1752 x1753 % x1786
                  &&& (x1788 === pair x1752 x1753 % x1786)
                  &&& _________________________________lookupoLookupo y835 y836 y837 x1787 y838 y839 x1788 y840 y841 ) ) ) )
  and _________________________________lookupoLookupo y842 y843 y844 y845 y846 y847 y848 y849 y850 =
    y846 === y842 &&& (y847 === !!true) &&& ________________lookupo y842 y843 y844 y848 y849 y850
    ||| ( y846 === y843 &&& (y847 === y844) &&& ________________lookupo y842 y843 y844 y848 y849 y850
        ||| __________________________________lookupoLookupo y845 y846 y847 y842 y843 y844 y848 y849 y850 )
  and __________________________________lookupoLookupo y851 y852 y853 y854 y855 y856 y857 y858 y859 =
    fresh (x1802 x1801 x1803)
      ( y851
      === pair y852 y853 % x1803
      &&& ________________lookupo y854 y855 y856 y857 y858 y859
      ||| (y851 === pair x1801 x1802 % x1803 &&& __________________________________lookupoLookupo x1803 y852 y853 y854 y855 y856 y857 y858 y859) )
  and lookupoLookupoLookupoLookupo y860 y861 y862 y863 y864 y865 y866 y867 y868 =
    fresh (x1904 x1903 x1902 x1901 x1810 x1809 x1811)
      ( y860
      === pair y861 !!true % x1811
      &&& __________lookupoLookupoLookupo y862 y863 y861 x1811 y864 y865 y866 y867 y868
      ||| ( y860
          === pair x1809 x1810 % x1901
          &&& ( x1902
              === pair x1809 x1810 % x1901
              &&& (x1903 === pair x1809 x1810 % x1901)
              &&& (x1904 === pair x1809 x1810 % x1901)
              &&& lookupo x1901 y861
              &&& ( x1902
                  === pair x1809 x1810 % x1901
                  &&& (x1903 === pair x1809 x1810 % x1901)
                  &&& (x1904 === pair x1809 x1810 % x1901)
                  &&& _______lookupoLookupoLookupo y862 y863 x1902 y864 x1903 y865 y866 x1904 y867 y868 ) ) ) )
  and __________lookupoLookupoLookupo y869 y870 y871 y872 y873 y874 y875 y876 y877 =
    fresh
      (x1882 x1881 x1880 x1847 x1846 x1876 x1875 x1866 x1865 x1867 x1848)
      ( y873 === y869 &&& (y870 === !!false)
      &&& ___________________________________lookupoLookupo y869 y871 y872 y874 y875 y876 y877
      ||| ( y872
          === pair y873 !!false % x1848
          &&& ( y874 === y869 &&& (y875 === y870)
              &&& __________________lookupo y869 y870 y871 y873 x1848 y876 y877
              ||| ( y874 === y871 &&& (y875 === !!true)
                  &&& __________________lookupo y869 y870 y871 y873 x1848 y876 y877
                  ||| ( y874 === y873 &&& (y875 === !!false)
                      &&& __________________lookupo y869 y870 y871 y873 x1848 y876 y877
                      ||| ( x1848
                          === pair y874 y875 % x1867
                          &&& (y876 === y869 &&& (y877 === y870) ||| ___________________________lookupo y871 y873 y874 y875 x1867 y876 y877)
                          ||| ( x1848
                              === pair x1865 x1866 % x1875
                              &&& ( x1876
                                  === pair x1865 x1866 % x1875
                                  &&& _lookupo x1875 y874 y875
                                  &&& (x1876 === pair x1865 x1866 % x1875 &&& __________________lookupo y869 y870 y871 y873 x1876 y876 y877) ) ) ) ) ) )
          ||| ( y872
              === pair x1846 x1847 % x1880
              &&& ( x1881
                  === pair x1846 x1847 % x1880
                  &&& (x1882 === pair x1846 x1847 % x1880)
                  &&& __lookupo x1880 y873
                  &&& ( x1881
                      === pair x1846 x1847 % x1880
                      &&& (x1882 === pair x1846 x1847 % x1880)
                      &&& ____________________________________lookupoLookupo y869 y870 y871 x1881 y874 y875 x1882 y876 y877 ) ) ) ) )
  and ___________________________________lookupoLookupo y878 y879 y880 y881 y882 y883 y884 =
    fresh (x1838 x1837 x1828 x1827 x1829)
      ( y881 === y878 &&& (y882 === !!false) &&& _________________lookupo y878 y879 y880 y883 y884
      ||| ( y881 === y879 &&& (y882 === !!true) &&& _________________lookupo y878 y879 y880 y883 y884
          ||| ( y880
              === pair y881 y882 % x1829
              &&& ____________________________lookupo y878 y879 y881 y882 x1829 y883 y884
              ||| ( y880
                  === pair x1827 x1828 % x1837
                  &&& ( x1838
                      === pair x1827 x1828 % x1837
                      &&& _lookupo x1837 y881 y882
                      &&& (x1838 === pair x1827 x1828 % x1837 &&& _________________lookupo y878 y879 x1838 y883 y884) ) ) ) ) )
  and ____________________________lookupo y885 y886 y887 y888 y889 y890 y891 =
    y890 === y885 &&& (y891 === !!false) ||| ________________lookupo y886 y887 y888 y889 y890 y891
  and ____________________________________lookupoLookupo y892 y893 y894 y895 y896 y897 y898 y899 y900 =
    y896 === y892 &&& (y897 === y893) &&& _________lookupo y892 y893 y894 y898 y899 y900
    ||| ( y896 === y894 &&& (y897 === !!true) &&& _________lookupo y892 y893 y894 y898 y899 y900
        ||| _____________________________________lookupoLookupo y895 y896 y897 y892 y893 y894 y898 y899 y900 )
  and _____________________________________lookupoLookupo y901 y902 y903 y904 y905 y906 y907 y908 y909 =
    fresh (x1896 x1895 x1897)
      ( y901
      === pair y902 y903 % x1897
      &&& _________lookupo y904 y905 y906 y907 y908 y909
      ||| (y901 === pair x1895 x1896 % x1897 &&& _____________________________________lookupoLookupo x1897 y902 y903 y904 y905 y906 y907 y908 y909) )
  and ______lookupoNotoLookupoLookupo y910 y911 y912 y913 y914 y915 y916 y917 =
    fresh (x1918 x1917 x1919)
      ( y911
      === pair y912 !!true % x1919
      &&& (y913 === !!false &&& ___________________________________lookupoLookupo y910 y912 x1919 y914 y915 y916 y917)
      ||| (y911 === pair x1917 x1918 % x1919 &&& (___________lookupoLookupoLookupo x1919 y912 y910 x1917 x1918 y914 y915 y916 y917 &&& ___noto y913)) )
  and ___________lookupoLookupoLookupo y918 y919 y920 y921 y922 y923 y924 y925 y926 =
    fresh
      (x1960 x1959 x1958 x1925 x1924 x1954 x1953 x1944 x1943 x1945 x1926)
      ( y918
      === pair y919 !!true % x1926
      &&& ( y923 === y920 &&& (y924 === !!false)
          &&& ___________________lookupo y920 y921 y922 y919 x1926 y925 y926
          ||| ( y923 === y921 &&& (y924 === y922)
              &&& ___________________lookupo y920 y921 y922 y919 x1926 y925 y926
              ||| ( y923 === y919 &&& (y924 === !!true)
                  &&& ___________________lookupo y920 y921 y922 y919 x1926 y925 y926
                  ||| ( x1926
                      === pair y923 y924 % x1945
                      &&& (y925 === y920 &&& (y926 === !!false) ||| _________________________lookupo y921 y922 y919 y923 y924 x1945 y925 y926)
                      ||| ( x1926
                          === pair x1943 x1944 % x1953
                          &&& ( x1954
                              === pair x1943 x1944 % x1953
                              &&& _lookupo x1953 y923 y924
                              &&& (x1954 === pair x1943 x1944 % x1953 &&& ___________________lookupo y920 y921 y922 y919 x1954 y925 y926) ) ) ) ) ) )
      ||| ( y918
          === pair x1924 x1925 % x1958
          &&& ( x1959
              === pair x1924 x1925 % x1958
              &&& (x1960 === pair x1924 x1925 % x1958)
              &&& lookupo x1958 y919
              &&& ( x1959
                  === pair x1924 x1925 % x1958
                  &&& (x1960 === pair x1924 x1925 % x1958)
                  &&& __________________________lookupoLookupo y920 y921 y922 x1959 y923 y924 x1960 y925 y926 ) ) ) )
  and _lookupoLookupoLookupoLookupo y927 y928 y929 y930 y931 y932 y933 y934 y935 =
    fresh (x2022 x2021 x2020 x2019 x1967 x1966 x1968)
      ( y927
      === pair y928 !!false % x1968
      &&& ____________lookupoLookupoLookupo y929 y930 y928 x1968 y931 y932 y933 y934 y935
      ||| ( y927
          === pair x1966 x1967 % x2019
          &&& ( x2020
              === pair x1966 x1967 % x2019
              &&& (x2021 === pair x1966 x1967 % x2019)
              &&& (x2022 === pair x1966 x1967 % x2019)
              &&& __lookupo x2019 y928
              &&& ( x2020
                  === pair x1966 x1967 % x2019
                  &&& (x2021 === pair x1966 x1967 % x2019)
                  &&& (x2022 === pair x1966 x1967 % x2019)
                  &&& _____________lookupoLookupoLookupo y929 y930 x2020 y931 x2021 y932 y933 x2022 y934 y935 ) ) ) )
  and ____________lookupoLookupoLookupo y936 y937 y938 y939 y940 y941 y942 y943 y944 =
    fresh
      (x2015 x2014 x2013 x1980 x1979 x2009 x2008 x1999 x1998 x2000 x1981)
      ( y940 === y936 &&& (y937 === !!true)
      &&& ________________________________lookupoLookupo y936 y938 y939 y941 y942 y943 y944
      ||| ( y939
          === pair y940 !!true % x1981
          &&& ( y941 === y936 &&& (y942 === y937)
              &&& ____________________lookupo y936 y937 y938 y940 x1981 y943 y944
              ||| ( y941 === y938 &&& (y942 === !!false)
                  &&& ____________________lookupo y936 y937 y938 y940 x1981 y943 y944
                  ||| ( y941 === y940 &&& (y942 === !!true)
                      &&& ____________________lookupo y936 y937 y938 y940 x1981 y943 y944
                      ||| ( x1981
                          === pair y941 y942 % x2000
                          &&& (y943 === y936 &&& (y944 === y937) ||| ____________________________lookupo y938 y940 y941 y942 x2000 y943 y944)
                          ||| ( x1981
                              === pair x1998 x1999 % x2008
                              &&& ( x2009
                                  === pair x1998 x1999 % x2008
                                  &&& _lookupo x2008 y941 y942
                                  &&& (x2009 === pair x1998 x1999 % x2008 &&& ____________________lookupo y936 y937 y938 y940 x2009 y943 y944) ) ) ) ) ) )
          ||| ( y939
              === pair x1979 x1980 % x2013
              &&& ( x2014
                  === pair x1979 x1980 % x2013
                  &&& (x2015 === pair x1979 x1980 % x2013)
                  &&& lookupo x2013 y940
                  &&& ( x2014
                      === pair x1979 x1980 % x2013
                      &&& (x2015 === pair x1979 x1980 % x2013)
                      &&& ____________________________lookupoLookupo y936 y937 y938 x2014 y941 y942 x2015 y943 y944 ) ) ) ) )
  and _____________lookupoLookupoLookupo y945 y946 y947 y948 y949 y950 y951 y952 y953 y954 =
    y948 === y945 &&& (y946 === !!true)
    &&& ______________________________________lookupoLookupo y945 y949 y950 y951 y952 y953 y954
    ||| ______________lookupoLookupoLookupo y947 y948 y945 y946 y949 y950 y951 y952 y953 y954
  and ______________________________________lookupoLookupo y955 y956 y957 y958 y959 y960 y961 =
    y957 === y955 &&& (y958 === !!true) &&& _____lookupo y955 y959 y960 y961
    ||| _______________________________________lookupoLookupo y956 y957 y958 y955 y959 y960 y961
  and _______________________________________lookupoLookupo y962 y963 y964 y965 y966 y967 y968 =
    fresh (x2035 x2034 x2036)
      ( y962
      === pair y963 y964 % x2036
      &&& _____lookupo y965 y966 y967 y968
      ||| (y962 === pair x2034 x2035 % x2036 &&& _______________________________________lookupoLookupo x2036 y963 y964 y965 y966 y967 y968) )
  and ______________lookupoLookupoLookupo y969 y970 y971 y972 y973 y974 y975 y976 y977 y978 =
    fresh (x2041 x2040 x2042)
      ( y969
      === pair y970 !!true % x2042
      &&& ______________________lookupoLookupo y971 y972 y973 y974 y975 y976 y977 y978
      ||| (y969 === pair x2040 x2041 % x2042 &&& ______________lookupoLookupoLookupo x2042 y970 y971 y972 y973 y974 y975 y976 y977 y978) )
  and _lookupoLookupoNotoLookupoLookupo y979 y980 y981 y982 y983 y984 y985 y986 =
    fresh
      (x2186 x2185 x2184 x2183 x2130 x2129 x2131 x2048 x2047 x2049)
      ( y979
      === pair y980 !!true % x2049
      &&& _______lookupoNotoLookupoLookupo y980 x2049 y981 y982 y983 y984 y985 y986
      ||| ( y979
          === pair x2047 x2048 % x2049
          &&& ( x2049
              === pair y980 !!true % x2131
              &&& ________________lookupoLookupoLookupo x2047 x2048 y980 x2131 y981 y983 y984 y985 y986
              ||| ( x2049
                  === pair x2129 x2130 % x2183
                  &&& ( x2184
                      === pair x2129 x2130 % x2183
                      &&& (x2185 === pair x2129 x2130 % x2183)
                      &&& (x2186 === pair x2129 x2130 % x2183)
                      &&& lookupo x2183 y980
                      &&& ( x2184
                          === pair x2129 x2130 % x2183
                          &&& (x2185 === pair x2129 x2130 % x2183)
                          &&& (x2186 === pair x2129 x2130 % x2183)
                          &&& _____________lookupoLookupoLookupo x2047 x2048 x2184 y981 x2185 y983 y984 x2186 y985 y986 ) ) )
              &&& ___noto y982 ) ) )
  and _______lookupoNotoLookupoLookupo y987 y988 y989 y990 y991 y992 y993 y994 =
    fresh (x2057 x2056 x2058)
      ( y989 === y987
      &&& ____notoLookupoLookupo y990 y987 y988 y991 y992 y993 y994
      ||| ( y988
          === pair y989 !!true % x2058
          &&& (y990 === !!false &&& ________________________________________lookupoLookupo y987 y989 x2058 y991 y992 y993 y994)
          ||| (y988 === pair x2056 x2057 % x2058 &&& (_______________lookupoLookupoLookupo x2058 y989 y987 x2056 x2057 y991 y992 y993 y994 &&& ___noto y990))
          ) )
  and ________________________________________lookupoLookupo y995 y996 y997 y998 y999 y1000 y1001 =
    fresh (x2082 x2081 x2072 x2071 x2073)
      ( y998 === y995 &&& (y999 === !!true)
      &&& _____________________lookupo y995 y996 y997 y1000 y1001
      ||| ( y998 === y996 &&& (y999 === !!true)
          &&& _____________________lookupo y995 y996 y997 y1000 y1001
          ||| ( y997
              === pair y998 y999 % x2073
              &&& _____________________________lookupo y995 y996 y998 y999 x2073 y1000 y1001
              ||| ( y997
                  === pair x2071 x2072 % x2081
                  &&& ( x2082
                      === pair x2071 x2072 % x2081
                      &&& _lookupo x2081 y998 y999
                      &&& (x2082 === pair x2071 x2072 % x2081 &&& _____________________lookupo y995 y996 x2082 y1000 y1001) ) ) ) ) )
  and _____________________________lookupo y1002 y1003 y1004 y1005 y1006 y1007 y1008 =
    y1007 === y1002 &&& (y1008 === !!true) ||| ________________lookupo y1003 y1004 y1005 y1006 y1007 y1008
  and _______________lookupoLookupoLookupo y1009 y1010 y1011 y1012 y1013 y1014 y1015 y1016 y1017 =
    fresh
      (x2123 x2122 x2121 x2088 x2087 x2117 x2116 x2107 x2106 x2108 x2089)
      ( y1009
      === pair y1010 !!true % x2089
      &&& ( y1014 === y1011 &&& (y1015 === !!true)
          &&& ______________________lookupo y1011 y1012 y1013 y1010 x2089 y1016 y1017
          ||| ( y1014 === y1012 &&& (y1015 === y1013)
              &&& ______________________lookupo y1011 y1012 y1013 y1010 x2089 y1016 y1017
              ||| ( y1014 === y1010 &&& (y1015 === !!true)
                  &&& ______________________lookupo y1011 y1012 y1013 y1010 x2089 y1016 y1017
                  ||| ( x2089
                      === pair y1014 y1015 % x2108
                      &&& (y1016 === y1011 &&& (y1017 === !!true) ||| _________________________lookupo y1012 y1013 y1010 y1014 y1015 x2108 y1016 y1017)
                      ||| ( x2089
                          === pair x2106 x2107 % x2116
                          &&& ( x2117
                              === pair x2106 x2107 % x2116
                              &&& _lookupo x2116 y1014 y1015
                              &&& (x2117 === pair x2106 x2107 % x2116 &&& ______________________lookupo y1011 y1012 y1013 y1010 x2117 y1016 y1017) ) ) ) ) ) )
      ||| ( y1009
          === pair x2087 x2088 % x2121
          &&& ( x2122
              === pair x2087 x2088 % x2121
              &&& (x2123 === pair x2087 x2088 % x2121)
              &&& lookupo x2121 y1010
              &&& ( x2122
                  === pair x2087 x2088 % x2121
                  &&& (x2123 === pair x2087 x2088 % x2121)
                  &&& _________________________________lookupoLookupo y1011 y1012 y1013 x2122 y1014 y1015 x2123 y1016 y1017 ) ) ) )
  and ________________lookupoLookupoLookupo y1018 y1019 y1020 y1021 y1022 y1023 y1024 y1025 y1026 =
    fresh
      (x2179 x2178 x2177 x2144 x2143 x2173 x2172 x2163 x2162 x2164 x2145)
      ( y1022 === y1018 &&& (y1019 === !!true)
      &&& ________________________________________lookupoLookupo y1018 y1020 y1021 y1023 y1024 y1025 y1026
      ||| ( y1022 === y1020
          &&& ________________________lookupoLookupo y1018 y1019 y1020 y1021 y1023 y1024 y1025 y1026
          ||| ( y1021
              === pair y1022 !!true % x2145
              &&& ( y1023 === y1018 &&& (y1024 === y1019)
                  &&& _______________________lookupo y1018 y1019 y1020 y1022 x2145 y1025 y1026
                  ||| ( y1023 === y1020 &&& (y1024 === !!true)
                      &&& _______________________lookupo y1018 y1019 y1020 y1022 x2145 y1025 y1026
                      ||| ( y1023 === y1022 &&& (y1024 === !!true)
                          &&& _______________________lookupo y1018 y1019 y1020 y1022 x2145 y1025 y1026
                          ||| ( x2145
                              === pair y1023 y1024 % x2164
                              &&& (y1025 === y1018 &&& (y1026 === y1019) ||| _____________________________lookupo y1020 y1022 y1023 y1024 x2164 y1025 y1026)
                              ||| ( x2145
                                  === pair x2162 x2163 % x2172
                                  &&& ( x2173
                                      === pair x2162 x2163 % x2172
                                      &&& _lookupo x2172 y1023 y1024
                                      &&& (x2173 === pair x2162 x2163 % x2172 &&& _______________________lookupo y1018 y1019 y1020 y1022 x2173 y1025 y1026) )
                                  ) ) ) ) )
              ||| ( y1021
                  === pair x2143 x2144 % x2177
                  &&& ( x2178
                      === pair x2143 x2144 % x2177
                      &&& (x2179 === pair x2143 x2144 % x2177)
                      &&& lookupo x2177 y1022
                      &&& ( x2178
                          === pair x2143 x2144 % x2177
                          &&& (x2179 === pair x2143 x2144 % x2177)
                          &&& ____________________________________lookupoLookupo y1018 y1019 y1020 x2178 y1023 y1024 x2179 y1025 y1026 ) ) ) ) ) )
  and notoLookupoNotoLookupoLookupo y1027 y1028 y1029 y1030 y1031 y1032 y1033 = ____lookupoNotoLookupoLookupo y1027 y1028 y1029 y1030 y1031 y1032 y1033
  and _notoLookupoNotoLookupoLookupo y1034 y1035 y1036 y1037 y1038 y1039 y1040 = ___lookupoNotoLookupoLookupo y1034 y1035 y1036 y1037 y1038 y1039 y1040
  and lookupoNotoLookupoNotoLookupoLookupo y1041 y1042 y1043 y1044 y1045 y1046 y1047 y1048 y1049 =
    fresh
      (x2241 x2240 x2239 x2238 x2233 x2232 x2234 x2214 x2213 x2215)
      ( y1041
      === pair y1042 y1043 % x2215
      &&& (y1043 === !!true &&& ________lookupoNotoLookupoLookupo y1042 x2215 y1044 y1045 y1046 y1047 y1048 y1049)
      ||| ( y1041
          === pair x2213 x2214 % x2215
          &&& ( x2215
              === pair y1042 y1043 % x2234
              &&& (y1043 === !!true &&& __________lookupoLookupoLookupo x2213 x2214 y1042 x2234 y1044 y1046 y1047 y1048 y1049)
              ||| ( x2215
                  === pair x2232 x2233 % x2238
                  &&& ( x2239
                      === pair x2232 x2233 % x2238
                      &&& (x2240 === pair x2232 x2233 % x2238)
                      &&& (x2241 === pair x2232 x2233 % x2238)
                      &&& _lookupoNoto x2238 y1042 y1043
                      &&& ( x2239
                          === pair x2232 x2233 % x2238
                          &&& (x2240 === pair x2232 x2233 % x2238)
                          &&& (x2241 === pair x2232 x2233 % x2238)
                          &&& _______lookupoLookupoLookupo x2213 x2214 x2239 y1044 x2240 y1046 y1047 x2241 y1048 y1049 ) ) )
              &&& __noto y1045 ) ) )
  and ________lookupoNotoLookupoLookupo y1050 y1051 y1052 y1053 y1054 y1055 y1056 y1057 =
    fresh (x2223 x2222 x2224)
      ( y1051
      === pair y1052 !!false % x2224
      &&& (y1053 === !!true &&& ________________________________lookupoLookupo y1050 y1052 x2224 y1054 y1055 y1056 y1057)
      ||| (y1051 === pair x2222 x2223 % x2224 &&& (_________lookupoLookupoLookupo x2224 y1052 y1050 x2222 x2223 y1054 y1055 y1056 y1057 &&& __noto y1053)) )
  and lookupoNotoLookupoLookupoLookupo y1058 y1059 y1060 y1061 y1062 y1063 y1064 y1065 y1066 y1067 =
    fresh (x2275 x2274 x2273 x2272 x2267 x2266 x2268)
      ( y1058
      === pair y1059 y1060 % x2268
      &&& (y1060 === !!false &&& ______lookupoLookupoLookupo y1061 y1062 y1059 x2268 y1063 y1064 y1065 y1066 y1067)
      ||| ( y1058
          === pair x2266 x2267 % x2272
          &&& ( x2273
              === pair x2266 x2267 % x2272
              &&& (x2274 === pair x2266 x2267 % x2272)
              &&& (x2275 === pair x2266 x2267 % x2272)
              &&& lookupoNoto x2272 y1059 y1060
              &&& ( x2273
                  === pair x2266 x2267 % x2272
                  &&& (x2274 === pair x2266 x2267 % x2272)
                  &&& (x2275 === pair x2266 x2267 % x2272)
                  &&& _______lookupoLookupoLookupo y1061 y1062 x2273 y1063 x2274 y1064 y1065 x2275 y1066 y1067 ) ) ) )
  and _lookupoNotoLookupoLookupoLookupo y1068 y1069 y1070 y1071 y1072 y1073 y1074 y1075 y1076 y1077 =
    fresh (x2296 x2295 x2294 x2293 x2288 x2287 x2289)
      ( y1068
      === pair y1069 y1070 % x2289
      &&& (y1070 === !!true &&& ________________lookupoLookupoLookupo y1071 y1072 y1069 x2289 y1073 y1074 y1075 y1076 y1077)
      ||| ( y1068
          === pair x2287 x2288 % x2293
          &&& ( x2294
              === pair x2287 x2288 % x2293
              &&& (x2295 === pair x2287 x2288 % x2293)
              &&& (x2296 === pair x2287 x2288 % x2293)
              &&& _lookupoNoto x2293 y1069 y1070
              &&& ( x2294
                  === pair x2287 x2288 % x2293
                  &&& (x2295 === pair x2287 x2288 % x2293)
                  &&& (x2296 === pair x2287 x2288 % x2293)
                  &&& _____________lookupoLookupoLookupo y1071 y1072 x2294 y1073 x2295 y1074 y1075 x2296 y1076 y1077 ) ) ) )
  and _lookupoNotoLookupoNotoLookupoLookupo y1078 y1079 y1080 y1081 y1082 y1083 y1084 y1085 y1086 =
    fresh
      (x2317 x2316 x2315 x2314 x2309 x2308 x2310 x2302 x2301 x2303)
      ( y1078
      === pair y1079 y1080 % x2303
      &&& (y1080 === !!false &&& ______lookupoNotoLookupoLookupo y1079 x2303 y1081 y1082 y1083 y1084 y1085 y1086)
      ||| ( y1078
          === pair x2301 x2302 % x2303
          &&& ( x2303
              === pair y1079 y1080 % x2310
              &&& (y1080 === !!false &&& ____________lookupoLookupoLookupo x2301 x2302 y1079 x2310 y1081 y1083 y1084 y1085 y1086)
              ||| ( x2303
                  === pair x2308 x2309 % x2314
                  &&& ( x2315
                      === pair x2308 x2309 % x2314
                      &&& (x2316 === pair x2308 x2309 % x2314)
                      &&& (x2317 === pair x2308 x2309 % x2314)
                      &&& lookupoNoto x2314 y1079 y1080
                      &&& ( x2315
                          === pair x2308 x2309 % x2314
                          &&& (x2316 === pair x2308 x2309 % x2314)
                          &&& (x2317 === pair x2308 x2309 % x2314)
                          &&& _____________lookupoLookupoLookupo x2301 x2302 x2315 y1081 x2316 y1083 y1084 x2317 y1085 y1086 ) ) )
              &&& ___noto y1082 ) ) )
  and logintoNotoNotoLookupoLookupoLookupo y1087 y1088 y1089 y1090 y1091 y1092 y1093 y1094 y1095 y1096 y1097 =
    fresh
      (x2490 x2489 x2487 x2485 x2424 x2423 x2421 x2419 x2406 x2404 x2398 x2397 x2396 x2395 x2337 x2336 x2391 x2390 x2389 x2375 x2374 x2376 x2364 x2363 x2362
         x2348 x2347 x2349 x2338 x2324)
      ( y1088 === ltrue () &&& (y1089 === !!true)
      &&& (y1090 === !!false &&& (y1091 === !!true &&& __lookupoLookupoLookupo y1087 y1092 y1093 y1094 y1095 y1096 y1097))
      ||| ( y1088 === lfalse () &&& (y1089 === !!false)
          &&& (y1090 === !!true &&& (y1091 === !!false &&& __lookupoLookupoLookupo y1087 y1092 y1093 y1094 y1095 y1096 y1097))
          ||| ( y1088 === var x2324
              &&& ( y1087
                  === pair x2324 y1089 % x2338
                  &&& ( y1089 === !!true &&& (y1090 === !!false)
                      &&& ( y1091 === !!true
                          &&& ( y1092 === x2324 &&& (y1093 === !!true)
                              &&& _________________lookupoLookupo x2324 x2338 y1094 y1095 y1096 y1097
                              ||| ( x2338
                                  === pair y1092 y1093 % x2349
                                  &&& ( y1094 === x2324 &&& (y1095 === !!true)
                                      &&& ________________lookupo x2324 y1092 y1093 x2349 y1096 y1097
                                      ||| ( y1094 === y1092 &&& (y1095 === y1093)
                                          &&& ________________lookupo x2324 y1092 y1093 x2349 y1096 y1097
                                          ||| __________________lookupoLookupo x2349 y1094 y1095 x2324 y1092 y1093 y1096 y1097 ) )
                                  ||| ( x2338
                                      === pair x2347 x2348 % x2362
                                      &&& ( x2363
                                          === pair x2347 x2348 % x2362
                                          &&& (x2364 === pair x2347 x2348 % x2362)
                                          &&& _lookupo x2362 y1092 y1093
                                          &&& ( x2363
                                              === pair x2347 x2348 % x2362
                                              &&& (x2364 === pair x2347 x2348 % x2362)
                                              &&& ______________________________________lookupoLookupo x2324 x2363 y1094 y1095 x2364 y1096 y1097 ) ) ) ) ) )
                      ||| ( y1089 === !!false &&& (y1090 === !!true)
                          &&& ( y1091 === !!false
                              &&& ( y1092 === x2324 &&& (y1093 === !!false)
                                  &&& ___________________lookupoLookupo x2324 x2338 y1094 y1095 y1096 y1097
                                  ||| ( x2338
                                      === pair y1092 y1093 % x2376
                                      &&& ( y1094 === x2324 &&& (y1095 === !!false)
                                          &&& ____________lookupo x2324 y1092 y1093 x2376 y1096 y1097
                                          ||| ( y1094 === y1092 &&& (y1095 === y1093)
                                              &&& ____________lookupo x2324 y1092 y1093 x2376 y1096 y1097
                                              ||| ____________________lookupoLookupo x2376 y1094 y1095 x2324 y1092 y1093 y1096 y1097 ) )
                                      ||| ( x2338
                                          === pair x2374 x2375 % x2389
                                          &&& ( x2390
                                              === pair x2374 x2375 % x2389
                                              &&& (x2391 === pair x2374 x2375 % x2389)
                                              &&& _lookupo x2389 y1092 y1093
                                              &&& ( x2390
                                                  === pair x2374 x2375 % x2389
                                                  &&& (x2391 === pair x2374 x2375 % x2389)
                                                  &&& ______________________________lookupoLookupo x2324 x2390 y1094 y1095 x2391 y1096 y1097 ) ) ) ) ) ) ) )
                  ||| ( y1087
                      === pair x2336 x2337 % x2395
                      &&& ( x2396
                          === pair x2336 x2337 % x2395
                          &&& (x2397 === pair x2336 x2337 % x2395)
                          &&& (x2398 === pair x2336 x2337 % x2395)
                          &&& lookupoNotoNoto x2395 x2324 y1089 y1090 y1091
                          &&& ( x2396
                              === pair x2336 x2337 % x2395
                              &&& (x2397 === pair x2336 x2337 % x2395)
                              &&& (x2398 === pair x2336 x2337 % x2395)
                              &&& _lookupo x2396 y1092 y1093
                              &&& ( x2396
                                  === pair x2336 x2337 % x2395
                                  &&& (x2397 === pair x2336 x2337 % x2395)
                                  &&& (x2398 === pair x2336 x2337 % x2395)
                                  &&& _lookupo x2397 y1094 y1095
                                  &&& ( x2396
                                      === pair x2336 x2337 % x2395
                                      &&& (x2397 === pair x2336 x2337 % x2395)
                                      &&& (x2398 === pair x2336 x2337 % x2395)
                                      &&& _lookupo x2398 y1096 y1097 ) ) ) ) ) )
              ||| ( y1088 === neg x2404
                  &&& (logintoNotoNotoLookupoLookupoLookupo y1087 x2404 x2406 y1089 y1090 y1092 y1093 y1094 y1095 y1096 y1097 &&& _noto y1090 y1091)
                  ||| ( y1088 === conj x2419 x2421
                      &&& ( logintoLogintoAndoNotoLookupo y1087 x2419 x2423 x2421 x2424 y1089 y1090 y1092 y1093
                          &&& (_noto y1090 y1091 &&& _lookupoLookupo y1087 y1094 y1095 y1096 y1097) )
                      ||| ( y1088 === disj x2485 x2487
                          &&& ( logintoLogintoOroNotoLookupoLookupo y1087 x2485 x2489 x2487 x2490 y1089 y1090 y1092 y1093 y1094 y1095
                              &&& (_noto y1090 y1091 &&& _lookupo y1087 y1096 y1097) ) ) ) ) ) ) )
  and __oroNoto y1098 y1099 y1100 y1101 =
    y1098 === !!false &&& (y1099 === !!false) &&& (y1100 === !!false) &&& __noto y1101
    ||| ( y1098 === !!false &&& (y1099 === !!true) &&& (y1100 === !!true) &&& ___noto y1101
        ||| ( y1098 === !!true &&& (y1099 === !!false) &&& (y1100 === !!true) &&& ___noto y1101
            ||| (y1098 === !!true &&& (y1099 === !!true) &&& (y1100 === !!true) &&& ___noto y1101) ) )
  and _________________________________________lookupoLookupo y1102 y1103 y1104 y1105 =
    fresh (x2657 x2656 x2658)
      ( y1102
      === pair y1103 !!false % x2658
      &&& ______lookupo y1103 x2658 y1104 y1105
      ||| (y1102 === pair x2656 x2657 % x2658 &&& ___lookupoLookupo x2658 y1103 x2656 x2657 y1104 y1105) )
  and __________________________________________lookupoLookupo y1106 y1107 y1108 y1109 =
    fresh (x2664 x2663 x2665)
      ( y1106
      === pair y1107 !!true % x2665
      &&& _____lookupo y1107 x2665 y1108 y1109
      ||| (y1106 === pair x2663 x2664 % x2665 &&& ____lookupoLookupo x2665 y1107 x2663 x2664 y1108 y1109) )
  and oroLookupo y1110 y1111 y1112 y1113 y1114 =
    y1110 === !!false &&& (y1111 === !!false) &&& (y1112 === !!false) &&& __lookupo y1113 y1114
    ||| ( y1110 === !!false &&& (y1111 === !!true) &&& (y1112 === !!true) &&& __lookupo y1113 y1114
        ||| ( y1110 === !!true &&& (y1111 === !!false) &&& (y1112 === !!true) &&& lookupo y1113 y1114
            ||| (y1110 === !!true &&& (y1111 === !!true) &&& (y1112 === !!true) &&& lookupo y1113 y1114) ) )
  and logintoOroLookupo y1115 y1116 y1117 y1118 y1119 y1120 y1121 =
    fresh
      (x2759 x2760 x2757 x2720 x2723 x2743 x2721 x2742 x2737 x2736 x2719)
      ( y1116 === ltrue () &&& (y1117 === !!true)
      &&& (y1118 === !!false &&& (y1119 === !!true) &&& _lookupo y1115 y1120 y1121 ||| (y1118 === !!true &&& (y1119 === !!true) &&& _lookupo y1115 y1120 y1121))
      ||| ( y1116 === lfalse () &&& (y1117 === !!false)
          &&& ( y1118 === !!false &&& (y1119 === !!false) &&& _lookupo y1115 y1120 y1121
              ||| (y1118 === !!true &&& (y1119 === !!true) &&& _lookupo y1115 y1120 y1121) )
          ||| ( y1116 === var x2719
              &&& ( y1118 === !!false &&& (y1117 === !!false) &&& (y1119 === !!false)
                  &&& _________________________________________lookupoLookupo y1115 x2719 y1120 y1121
                  ||| ( y1118 === !!false &&& (y1117 === !!true) &&& (y1119 === !!true)
                      &&& __________________________________________lookupoLookupo y1115 x2719 y1120 y1121
                      ||| ( y1118 === !!true &&& (y1117 === !!false) &&& (y1119 === !!true)
                          &&& _________________________________________lookupoLookupo y1115 x2719 y1120 y1121
                          ||| ( y1118 === !!true &&& (y1117 === !!true) &&& (y1119 === !!true)
                              &&& __________________________________________lookupoLookupo y1115 x2719 y1120 y1121 ) ) ) )
              ||| ( y1116 === neg x2736
                  &&& (logintoLookupo y1115 x2736 x2737 y1120 y1121 &&& (oro y1118 y1117 y1119 &&& _noto x2737 y1117))
                  ||| ( y1116 === conj x2742 x2721
                      &&& (logintoLookupo y1115 x2742 x2743 y1120 y1121 &&& (oro y1118 y1117 y1119 &&& logintoAndo y1115 x2721 x2723 x2743 y1117))
                      ||| ( y1116 === disj x2720 x2757
                          &&& (logintoOroLookupo y1115 x2757 x2760 x2759 y1117 y1120 y1121 &&& (_loginto y1115 x2757 x2760 &&& oro y1118 y1117 y1119)) ) ) ) )
          ) )
  and andoLookupo y1122 y1123 y1124 y1125 y1126 =
    y1122 === !!false &&& (y1123 === !!false) &&& (y1124 === !!false) &&& __lookupo y1125 y1126
    ||| ( y1122 === !!false &&& (y1123 === !!true) &&& (y1124 === !!false) &&& __lookupo y1125 y1126
        ||| ( y1122 === !!true &&& (y1123 === !!false) &&& (y1124 === !!false) &&& lookupo y1125 y1126
            ||| (y1122 === !!true &&& (y1123 === !!true) &&& (y1124 === !!true) &&& lookupo y1125 y1126) ) )
  and logintoLogintoLookupo y1127 y1128 y1129 y1130 y1131 y1132 y1133 =
    fresh
      (x2854 x2852 x2853 x2851 x2842 x2840 x2841 x2839 x2835 x2834 x2826 x2824 x2823 x2825 x2821 x2822 x2813)
      ( y1128 === ltrue () &&& (y1129 === !!true) &&& logintoLookupo y1127 y1130 y1131 y1132 y1133
      ||| ( y1128 === lfalse () &&& (y1129 === !!false) &&& logintoLookupo y1127 y1130 y1131 y1132 y1133
          ||| ( y1128 === var x2813
              &&& ( y1130 === ltrue () &&& (y1131 === !!true) &&& _lookupoLookupo y1127 x2813 y1129 y1132 y1133
                  ||| ( y1130 === lfalse () &&& (y1131 === !!false) &&& _lookupoLookupo y1127 x2813 y1129 y1132 y1133
                      ||| ( y1130 === var x2822
                          &&& __lookupoLookupoLookupo y1127 x2822 y1131 x2813 y1129 y1132 y1133
                          ||| ( y1130 === neg x2821
                              &&& logintoNotoLookupoLookupo y1127 x2821 x2825 y1131 x2813 y1129 y1132 y1133
                              ||| ( y1130 === conj x2823 x2824
                                  &&& logintoLogintoAndoLookupoLookupo y1127 x2823 x2825 x2824 x2826 y1131 x2813 y1129 y1132 y1133
                                  ||| ( y1130 === disj x2823 x2824
                                      &&& logintoLogintoOroLookupoLookupo y1127 x2823 x2825 x2824 x2826 y1131 x2813 y1129 y1132 y1133 ) ) ) ) ) )
              ||| ( y1128 === neg x2834
                  &&& (logintoLogintoLookupo y1127 x2834 x2835 y1130 y1131 y1132 y1133 &&& _noto x2835 y1129)
                  ||| ( y1128 === conj x2839 x2841
                      &&& (logintoLogintoLookupo y1127 x2839 x2840 x2841 x2842 y1132 y1133 &&& (ando x2840 x2842 y1129 &&& _loginto y1127 y1130 y1131))
                      ||| ( y1128 === disj x2851 x2853
                          &&& (logintoLogintoLookupo y1127 x2851 x2852 x2853 x2854 y1132 y1133 &&& (oro x2852 x2854 y1129 &&& _loginto y1127 y1130 y1131)) ) )
                  ) ) ) )
  and logintoLogintoOroNotoLookupo y1134 y1135 y1136 y1137 y1138 y1139 y1140 y1141 y1142 =
    fresh
      (x3611 x3610 x3608 x3606 x2911 x2909 x2908 x2910 x2906 x3577 x3576 x3574 x3572 x3566 x3564 x3565 x3563 x3546 x3544 x3543 x3548 x3541 x3539 x3047 x3045
         x3044 x3046 x3042 x3086 x3085 x3087 x3064 x3063 x3074 x3073 x3075 x3065 x3002 x3043 x2998 x3034 x3033 x3035 x3014 x3013 x3022 x3021 x3023 x3015 x2999
         x2907 x2992 x2991 x2989 x2987 x2964 x2980 x2962 x2979 x2974 x2973 x2960 x2953 x2952 x2950 x2948 x2918 x2941 x2916 x2940 x2935 x2934 x2914)
      ( y1135 === ltrue () &&& (y1136 === !!true)
      &&& ( y1137 === ltrue () &&& (y1138 === !!true)
          &&& (y1139 === !!true &&& __notoLookupo y1140 y1134 y1141 y1142)
          ||| ( y1137 === lfalse () &&& (y1138 === !!false)
              &&& (y1139 === !!true &&& __notoLookupo y1140 y1134 y1141 y1142)
              ||| ( y1137 === var x2914
                  &&& ( y1138 === !!false &&& (y1139 === !!true)
                      &&& ________lookupoNotoLookupo y1134 x2914 y1140 y1141 y1142
                      ||| (y1138 === !!true &&& (y1139 === !!true) &&& __lookupoNotoLookupo y1134 x2914 y1140 y1141 y1142) )
                  ||| ( y1137 === neg x2934
                      &&& (logintoLookupo y1134 x2934 x2935 y1141 y1142 &&& (oroNoto y1138 y1139 y1140 &&& _noto x2935 y1138))
                      ||| ( y1137 === conj x2940 x2916
                          &&& (logintoLookupo y1134 x2940 x2941 y1141 y1142 &&& (oroNoto y1138 y1139 y1140 &&& logintoAndo y1134 x2916 x2918 x2941 y1138))
                          ||| ( y1137 === disj x2948 x2950
                              &&& (logintoLogintoOroLookupo y1134 x2948 x2952 x2950 x2953 y1138 y1141 y1142 &&& (_noto y1139 y1140 &&& _oro y1138 y1139)) ) )
                      ) ) ) )
      ||| ( y1135 === lfalse () &&& (y1136 === !!false)
          &&& ( y1137 === ltrue () &&& (y1138 === !!true)
              &&& (y1139 === !!true &&& __notoLookupo y1140 y1134 y1141 y1142)
              ||| ( y1137 === lfalse () &&& (y1138 === !!false)
                  &&& (y1139 === !!false &&& _notoLookupo y1140 y1134 y1141 y1142)
                  ||| ( y1137 === var x2960
                      &&& ( y1138 === !!false &&& (y1139 === !!false) &&& _lookupoNotoLookupo y1134 x2960 y1140 y1141 y1142
                          ||| (y1138 === !!true &&& (y1139 === !!true) &&& __lookupoNotoLookupo y1134 x2960 y1140 y1141 y1142) )
                      ||| ( y1137 === neg x2973
                          &&& (logintoLookupo y1134 x2973 x2974 y1141 y1142 &&& (_oroNoto y1138 y1139 y1140 &&& _noto x2974 y1138))
                          ||| ( y1137 === conj x2979 x2962
                              &&& (logintoLookupo y1134 x2979 x2980 y1141 y1142 &&& (_oroNoto y1138 y1139 y1140 &&& logintoAndo y1134 x2962 x2964 x2980 y1138))
                              ||| ( y1137 === disj x2987 x2989
                                  &&& (logintoLogintoOroLookupo y1134 x2987 x2991 x2989 x2992 y1138 y1141 y1142 &&& (_noto y1139 y1140 &&& __oro y1138 y1139))
                                  ) ) ) ) ) )
          ||| ( y1135 === var x2907
              &&& ( y1137 === ltrue () &&& (y1138 === !!true)
                  &&& ( y1136 === !!false &&& (y1139 === !!true)
                      &&& ________lookupoNotoLookupo y1134 x2907 y1140 y1141 y1142
                      ||| (y1136 === !!true &&& (y1139 === !!true) &&& __lookupoNotoLookupo y1134 x2907 y1140 y1141 y1142) )
                  ||| ( y1137 === lfalse () &&& (y1138 === !!false)
                      &&& ( y1136 === !!false &&& (y1139 === !!false) &&& _lookupoNotoLookupo y1134 x2907 y1140 y1141 y1142
                          ||| (y1136 === !!true &&& (y1139 === !!true) &&& __lookupoNotoLookupo y1134 x2907 y1140 y1141 y1142) )
                      ||| ( y1137 === var x2999
                          &&& ( y1136 === !!false &&& (y1138 === !!false) &&& (y1139 === !!false)
                              &&& lookupoLookupoNotoLookupo y1134 x2999 x2907 y1140 y1141 y1142
                              ||| ( y1136 === !!false &&& (y1138 === !!true) &&& (y1139 === !!true)
                                  &&& ( y1134
                                      === pair x2999 !!true % x3015
                                      &&& ( x3015
                                          === pair x2907 !!false % x3023
                                          &&& (y1140 === !!false &&& ______________lookupo x2999 x2907 x3023 y1141 y1142)
                                          ||| ( x3015
                                              === pair x3021 x3022 % x3023
                                              &&& (_________lookupoLookupo x3023 x2907 x2999 x3021 x3022 y1141 y1142 &&& ___noto y1140) ) )
                                      ||| ( y1134
                                          === pair x3013 x3014 % x3015
                                          &&& (lookupoLookupoLookupo x3015 x2999 x3013 x3014 x2907 y1141 y1142 &&& ___noto y1140) ) )
                                  ||| ( y1136 === !!true &&& (y1138 === !!false) &&& (y1139 === !!true)
                                      &&& ( y1134
                                          === pair x2999 !!false % x3035
                                          &&& _______lookupoNotoLookupo x2999 x3035 x2907 y1140 y1141 y1142
                                          ||| ( y1134
                                              === pair x3033 x3034 % x3035
                                              &&& (_lookupoLookupoLookupo x3035 x2999 x3033 x3034 x2907 y1141 y1142 &&& ___noto y1140) ) )
                                      ||| ( y1136 === !!true &&& (y1138 === !!true) &&& (y1139 === !!true)
                                          &&& _lookupoLookupoNotoLookupo y1134 x2999 x2907 y1140 y1141 y1142 ) ) ) )
                          ||| ( y1137 === neg x2998
                              &&& ( x2998 === ltrue ()
                                  &&& ( y1136 === !!false &&& (y1138 === !!false) &&& (y1139 === !!false)
                                      &&& notoLookupoNotoLookupo y1134 x2907 y1140 y1141 y1142
                                      ||| ( y1136 === !!true &&& (y1138 === !!false) &&& (y1139 === !!true)
                                          &&& __lookupoNotoLookupo y1134 x2907 y1140 y1141 y1142 ) )
                                  ||| ( x2998 === lfalse ()
                                      &&& ( y1136 === !!false &&& (y1138 === !!true) &&& (y1139 === !!true)
                                          &&& ________lookupoNotoLookupo y1134 x2907 y1140 y1141 y1142
                                          ||| ( y1136 === !!true &&& (y1138 === !!true) &&& (y1139 === !!true)
                                              &&& _notoLookupoNotoLookupo y1134 x2907 y1140 y1141 y1142 ) )
                                      ||| ( x2998 === var x3043
                                          &&& ( y1136 === !!false &&& (y1138 === !!false) &&& (y1139 === !!false)
                                              &&& lookupoNotoLookupoNotoLookupo y1134 x3043 x3002 x2907 y1140 y1141 y1142
                                              ||| ( y1136 === !!false &&& (y1138 === !!true) &&& (y1139 === !!true)
                                                  &&& ( y1134
                                                      === pair x3043 !!false % x3065
                                                      &&& ( x2907 === x3043 &&& ____notoLookupo y1140 x3043 x3065 y1141 y1142
                                                          ||| ( x3065
                                                              === pair x2907 !!false % x3075
                                                              &&& (y1140 === !!false &&& __________lookupo x3043 x2907 x3075 y1141 y1142)
                                                              ||| ( x3065
                                                                  === pair x3073 x3074 % x3075
                                                                  &&& (_____lookupoLookupo x3075 x2907 x3043 x3073 x3074 y1141 y1142 &&& ___noto y1140) ) ) )
                                                      ||| ( y1134
                                                          === pair x3063 x3064 % x3065
                                                          &&& (lookupoNotoLookupoLookupo x3065 x3043 x3002 x3063 x3064 x2907 y1141 y1142 &&& ___noto y1140) )
                                                      )
                                                  ||| ( y1136 === !!true &&& (y1138 === !!false) &&& (y1139 === !!true)
                                                      &&& ( y1134
                                                          === pair x3043 !!true % x3087
                                                          &&& ______lookupoNotoLookupo x3043 x3087 x2907 y1140 y1141 y1142
                                                          ||| ( y1134
                                                              === pair x3085 x3086 % x3087
                                                              &&& (_lookupoNotoLookupoLookupo x3087 x3043 x3002 x3085 x3086 x2907 y1141 y1142 &&& ___noto y1140)
                                                              ) )
                                                      ||| ( y1136 === !!true &&& (y1138 === !!true) &&& (y1139 === !!true)
                                                          &&& _lookupoNotoLookupoNotoLookupo y1134 x3043 x3002 x2907 y1140 y1141 y1142 ) ) ) )
                                          ||| ( x2998 === neg x3042
                                              &&& ( logintoNotoNotoLookupoLookupo y1134 x3042 x3046 x3002 y1138 x2907 y1136 y1141 y1142
                                                  &&& __oroNoto y1136 y1138 y1139 y1140 )
                                              ||| ( x2998 === conj x3044 x3045
                                                  &&& ( logintoLogintoAndoNotoLookupoLookupo y1134 x3044 x3046 x3045 x3047 x3002 y1138 x2907 y1136 y1141 y1142
                                                      &&& __oroNoto y1136 y1138 y1139 y1140 )
                                                  ||| ( x2998 === disj x3539 x3541
                                                      &&& ( __oroNoto y1136 y1138 y1139 y1140
                                                          &&& ( x3548 === x2907
                                                              &&& logintoLogintoOroNotoLookupo y1134 x3539 x3543 x3541 x3544 x3546 y1138 x3548 y1136
                                                              &&& _lookupo y1134 y1141 y1142 ) ) ) ) ) ) ) )
                              ||| ( y1137 === conj x3563 x3565
                                  &&& ( logintoLogintoLookupo y1134 x3563 x3564 x3565 x3566 y1141 y1142
                                      &&& (__oroNoto y1136 y1138 y1139 y1140 &&& (ando x3564 x3566 y1138 &&& _lookupo y1134 x2907 y1136)) )
                                  ||| ( y1137 === disj x3572 x3574
                                      &&& ( logintoLogintoOroLookupo y1134 x3572 x3576 x3574 x3577 y1138 y1141 y1142
                                          &&& (_noto y1139 y1140 &&& oroLookupo y1136 y1138 y1139 y1134 x2907) ) ) ) ) ) ) )
              ||| ( y1135 === neg x2906 &&& _noto x2910 y1136
                  ||| ( y1135 === conj x2908 x2909
                      &&& (ando x2910 x2911 y1136 &&& _loginto y1134 y1137 y1138)
                      ||| ( y1135 === disj x3606 x3608
                          &&& ( logintoLogintoOroLookupo y1134 x3606 x3610 x3608 x3611 y1136 y1141 y1142
                              &&& (_noto y1139 y1140 &&& logintoOro y1134 y1137 y1138 y1136 y1139) ) ) ) ) ) ) )
  and ________lookupoNotoLookupo y1143 y1144 y1145 y1146 y1147 =
    fresh (x2926 x2925 x2927)
      ( y1143
      === pair y1144 !!false % x2927
      &&& ____notoLookupo y1145 y1144 x2927 y1146 y1147
      ||| (y1143 === pair x2925 x2926 % x2927 &&& (___lookupoLookupo x2927 y1144 x2925 x2926 y1146 y1147 &&& ___noto y1145)) )
  and logintoLogintoAndoNotoLookupoLookupo y1148 y1149 y1150 y1151 y1152 y1153 y1154 y1155 y1156 y1157 y1158 =
    fresh
      (x3470 x3469 x3467 x3465 x3451 x3450 x3448 x3446 x3103 x3099 x3417 x3416 x3414 x3412 x3402 x3401 x3399 x3397 x3369 x3367 x3366 x3371 x3364 x3362 x3332
         x3330 x3329 x3334 x3327 x3325 x3273 x3269 x3300 x3299 x3310 x3309 x3311 x3301 x3291 x3290 x3292 x3229 x3270 x3225 x3249 x3248 x3257 x3256 x3258 x3250
         x3241 x3240 x3242 x3226 x3100 x3205 x3204 x3202 x3200 x3194 x3193 x3191 x3189 x3184 x3183 x3163 x3142 x3141 x3139 x3137 x3131 x3130 x3128 x3126 x3121
         x3120 x3107)
      ( y1149 === ltrue () &&& (y1150 === !!true)
      &&& ( y1151 === ltrue () &&& (y1152 === !!true)
          &&& (y1153 === !!true &&& _notoLookupoLookupo y1154 y1148 y1155 y1156 y1157 y1158)
          ||| ( y1151 === lfalse () &&& (y1152 === !!false)
              &&& (y1153 === !!false &&& notoLookupoLookupo y1154 y1148 y1155 y1156 y1157 y1158)
              ||| ( y1151 === var x3107
                  &&& ( y1152 === !!false &&& (y1153 === !!false)
                      &&& ____lookupoNotoLookupoLookupo y1148 x3107 y1154 y1155 y1156 y1157 y1158
                      ||| (y1152 === !!true &&& (y1153 === !!true) &&& ___lookupoNotoLookupoLookupo y1148 x3107 y1154 y1155 y1156 y1157 y1158) )
                  ||| ( y1151 === neg x3120
                      &&& (logintoLookupoLookupo y1148 x3120 x3121 y1155 y1156 y1157 y1158 &&& (andoNoto y1152 y1153 y1154 &&& _noto x3121 y1152))
                      ||| ( y1151 === conj x3126 x3128
                          &&& ( logintoLogintoAndoLookupoLookupo y1148 x3126 x3130 x3128 x3131 y1152 y1155 y1156 y1157 y1158
                              &&& (_noto y1153 y1154 &&& ___ando y1152 y1153) )
                          ||| ( y1151 === disj x3137 x3139
                              &&& ( logintoLogintoOroLookupo y1148 x3137 x3141 x3139 x3142 y1152 y1155 y1156
                                  &&& (_noto y1153 y1154 &&& (___ando y1152 y1153 &&& _lookupo y1148 y1157 y1158)) ) ) ) ) ) ) )
      ||| ( y1149 === lfalse () &&& (y1150 === !!false)
          &&& ( y1151 === ltrue () &&& (y1152 === !!true)
              &&& (y1153 === !!false &&& notoLookupoLookupo y1154 y1148 y1155 y1156 y1157 y1158)
              ||| ( y1151 === lfalse () &&& (y1152 === !!false)
                  &&& (y1153 === !!false &&& notoLookupoLookupo y1154 y1148 y1155 y1156 y1157 y1158)
                  ||| ( y1151 === var x3163
                      &&& ( y1152 === !!false &&& (y1153 === !!false)
                          &&& ____lookupoNotoLookupoLookupo y1148 x3163 y1154 y1155 y1156 y1157 y1158
                          ||| (y1152 === !!true &&& (y1153 === !!false) &&& _________lookupoNotoLookupoLookupo y1148 x3163 y1154 y1155 y1156 y1157 y1158) )
                      ||| ( y1151 === neg x3183
                          &&& (logintoLookupoLookupo y1148 x3183 x3184 y1155 y1156 y1157 y1158 &&& (_andoNoto y1152 y1153 y1154 &&& _noto x3184 y1152))
                          ||| ( y1151 === conj x3189 x3191
                              &&& ( logintoLogintoAndoLookupoLookupo y1148 x3189 x3193 x3191 x3194 y1152 y1155 y1156 y1157 y1158
                                  &&& (_noto y1153 y1154 &&& ____ando y1152 y1153) )
                              ||| ( y1151 === disj x3200 x3202
                                  &&& ( logintoLogintoOroLookupo y1148 x3200 x3204 x3202 x3205 y1152 y1155 y1156
                                      &&& (_noto y1153 y1154 &&& (____ando y1152 y1153 &&& _lookupo y1148 y1157 y1158)) ) ) ) ) ) ) )
          ||| ( y1149 === var x3100
              &&& ( y1151 === ltrue () &&& (y1152 === !!true)
                  &&& ( y1150 === !!false &&& (y1153 === !!false)
                      &&& ____lookupoNotoLookupoLookupo y1148 x3100 y1154 y1155 y1156 y1157 y1158
                      ||| (y1150 === !!true &&& (y1153 === !!true) &&& ___lookupoNotoLookupoLookupo y1148 x3100 y1154 y1155 y1156 y1157 y1158) )
                  ||| ( y1151 === lfalse () &&& (y1152 === !!false)
                      &&& ( y1150 === !!false &&& (y1153 === !!false)
                          &&& ____lookupoNotoLookupoLookupo y1148 x3100 y1154 y1155 y1156 y1157 y1158
                          ||| (y1150 === !!true &&& (y1153 === !!false) &&& _________lookupoNotoLookupoLookupo y1148 x3100 y1154 y1155 y1156 y1157 y1158) )
                      ||| ( y1151 === var x3226
                          &&& ( y1150 === !!false &&& (y1152 === !!false) &&& (y1153 === !!false)
                              &&& lookupoLookupoNotoLookupoLookupo y1148 x3226 x3100 y1154 y1155 y1156 y1157 y1158
                              ||| ( y1150 === !!false &&& (y1152 === !!true) &&& (y1153 === !!false)
                                  &&& ( y1148
                                      === pair x3226 !!true % x3242
                                      &&& ________lookupoNotoLookupoLookupo x3226 x3242 x3100 y1154 y1155 y1156 y1157 y1158
                                      ||| ( y1148
                                          === pair x3240 x3241 % x3242
                                          &&& (lookupoLookupoLookupoLookupo x3242 x3226 x3240 x3241 x3100 y1155 y1156 y1157 y1158 &&& __noto y1154) ) )
                                  ||| ( y1150 === !!true &&& (y1152 === !!false) &&& (y1153 === !!false)
                                      &&& ( y1148
                                          === pair x3226 !!false % x3250
                                          &&& ( x3250
                                              === pair x3100 !!true % x3258
                                              &&& ( y1154 === !!true
                                                  &&& ___________________________________lookupoLookupo x3226 x3100 x3258 y1155 y1156 y1157 y1158 )
                                              ||| ( x3250
                                                  === pair x3256 x3257 % x3258
                                                  &&& (___________lookupoLookupoLookupo x3258 x3100 x3226 x3256 x3257 y1155 y1156 y1157 y1158 &&& __noto y1154)
                                                  ) )
                                          ||| ( y1148
                                              === pair x3248 x3249 % x3250
                                              &&& (_lookupoLookupoLookupoLookupo x3250 x3226 x3248 x3249 x3100 y1155 y1156 y1157 y1158 &&& __noto y1154) ) )
                                      ||| ( y1150 === !!true &&& (y1152 === !!true) &&& (y1153 === !!true)
                                          &&& _lookupoLookupoNotoLookupoLookupo y1148 x3226 x3100 y1154 y1155 y1156 y1157 y1158 ) ) ) )
                          ||| ( y1151 === neg x3225
                              &&& ( x3225 === ltrue ()
                                  &&& ( y1150 === !!false &&& (y1152 === !!false) &&& (y1153 === !!false)
                                      &&& notoLookupoNotoLookupoLookupo y1148 x3100 y1154 y1155 y1156 y1157 y1158
                                      ||| ( y1150 === !!true &&& (y1152 === !!false) &&& (y1153 === !!false)
                                          &&& _________lookupoNotoLookupoLookupo y1148 x3100 y1154 y1155 y1156 y1157 y1158 ) )
                                  ||| ( x3225 === lfalse ()
                                      &&& ( y1150 === !!false &&& (y1152 === !!true) &&& (y1153 === !!false)
                                          &&& ____lookupoNotoLookupoLookupo y1148 x3100 y1154 y1155 y1156 y1157 y1158
                                          ||| ( y1150 === !!true &&& (y1152 === !!true) &&& (y1153 === !!true)
                                              &&& _notoLookupoNotoLookupoLookupo y1148 x3100 y1154 y1155 y1156 y1157 y1158 ) )
                                      ||| ( x3225 === var x3270
                                          &&& ( y1150 === !!false &&& (y1152 === !!false) &&& (y1153 === !!false)
                                              &&& lookupoNotoLookupoNotoLookupoLookupo y1148 x3270 x3229 x3100 y1154 y1155 y1156 y1157 y1158
                                              ||| ( y1150 === !!false &&& (y1152 === !!true) &&& (y1153 === !!false)
                                                  &&& ( y1148
                                                      === pair x3270 !!false % x3292
                                                      &&& _____lookupoNotoLookupoLookupo x3270 x3292 x3100 y1154 y1155 y1156 y1157 y1158
                                                      ||| ( y1148
                                                          === pair x3290 x3291 % x3292
                                                          &&& ( lookupoNotoLookupoLookupoLookupo x3292 x3270 x3229 x3290 x3291 x3100 y1155 y1156 y1157 y1158
                                                              &&& __noto y1154 ) ) )
                                                  ||| ( y1150 === !!true &&& (y1152 === !!false) &&& (y1153 === !!false)
                                                      &&& ( y1148
                                                          === pair x3270 !!true % x3301
                                                          &&& ( x3100 === x3270
                                                              &&& __notoLookupoLookupo y1154 x3270 x3301 y1155 y1156 y1157 y1158
                                                              ||| ( x3301
                                                                  === pair x3100 !!true % x3311
                                                                  &&& ( y1154 === !!true
                                                                      &&& ________________________________________lookupoLookupo x3270 x3100 x3311 y1155 y1156
                                                                            y1157 y1158 )
                                                                  ||| ( x3301
                                                                      === pair x3309 x3310 % x3311
                                                                      &&& ( _______________lookupoLookupoLookupo x3311 x3100 x3270 x3309 x3310 y1155 y1156
                                                                              y1157 y1158
                                                                          &&& __noto y1154 ) ) ) )
                                                          ||| ( y1148
                                                              === pair x3299 x3300 % x3301
                                                              &&& ( _lookupoNotoLookupoLookupoLookupo x3301 x3270 x3229 x3299 x3300 x3100 y1155 y1156 y1157
                                                                      y1158
                                                                  &&& __noto y1154 ) ) )
                                                      ||| ( y1150 === !!true &&& (y1152 === !!true) &&& (y1153 === !!true)
                                                          &&& _lookupoNotoLookupoNotoLookupoLookupo y1148 x3270 x3229 x3100 y1154 y1155 y1156 y1157 y1158 ) )
                                                  ) )
                                          ||| ( x3225 === neg x3269
                                              &&& ( logintoNotoNotoLookupoLookupoLookupo y1148 x3269 x3273 x3229 y1152 x3100 y1150 y1155 y1156 y1157 y1158
                                                  &&& __andoNoto y1150 y1152 y1153 y1154 )
                                              ||| ( x3225 === conj x3325 x3327
                                                  &&& ( __andoNoto y1150 y1152 y1153 y1154
                                                      &&& ( x3334 === x3100
                                                          &&& logintoLogintoAndoNotoLookupoLookupo y1148 x3325 x3329 x3327 x3330 x3332 y1152 x3334 y1150 y1155
                                                                y1156
                                                          &&& _lookupo y1148 y1157 y1158 ) )
                                                  ||| ( x3225 === disj x3362 x3364
                                                      &&& ( __andoNoto y1150 y1152 y1153 y1154
                                                          &&& ( x3371 === x3100
                                                              &&& logintoLogintoOroNotoLookupo y1148 x3362 x3366 x3364 x3367 x3369 y1152 x3371 y1150
                                                              &&& _lookupoLookupo y1148 y1155 y1156 y1157 y1158 ) ) ) ) ) ) ) )
                              ||| ( y1151 === conj x3397 x3399
                                  &&& ( logintoLogintoAndoLookupoLookupo y1148 x3397 x3401 x3399 x3402 y1152 y1155 y1156 y1157 y1158
                                      &&& (_noto y1153 y1154 &&& andoLookupo y1150 y1152 y1153 y1148 x3100) )
                                  ||| ( y1151 === disj x3412 x3414
                                      &&& ( logintoLogintoOroLookupo y1148 x3412 x3416 x3414 x3417 y1152 y1155 y1156
                                          &&& ( _noto y1153 y1154
                                              &&& ( y1150 === !!false &&& (y1152 === !!false) &&& (y1153 === !!false)
                                                  &&& _________________________________________lookupoLookupo y1148 x3100 y1157 y1158
                                                  ||| ( y1150 === !!false &&& (y1152 === !!true) &&& (y1153 === !!false)
                                                      &&& _________________________________________lookupoLookupo y1148 x3100 y1157 y1158
                                                      ||| ( y1150 === !!true &&& (y1152 === !!false) &&& (y1153 === !!false)
                                                          &&& __________________________________________lookupoLookupo y1148 x3100 y1157 y1158
                                                          ||| ( y1150 === !!true &&& (y1152 === !!true) &&& (y1153 === !!true)
                                                              &&& __________________________________________lookupoLookupo y1148 x3100 y1157 y1158 ) ) ) ) ) )
                                      ) ) ) ) ) )
              ||| ( y1149 === neg x3099 &&& _noto x3103 y1150
                  ||| ( y1149 === conj x3446 x3448
                      &&& ( logintoLogintoAndoLookupoLookupo y1148 x3446 x3450 x3448 x3451 y1150 y1155 y1156 y1157 y1158
                          &&& (_noto y1153 y1154 &&& logintoAndo y1148 y1151 y1152 y1150 y1153) )
                      ||| ( y1149 === disj x3465 x3467
                          &&& ( logintoLogintoOroLookupo y1148 x3465 x3469 x3467 x3470 y1150 y1155 y1156
                              &&& (_noto y1153 y1154 &&& logintoAndoLookupo y1148 y1151 y1152 y1150 y1153 y1157 y1158) ) ) ) ) ) ) )
  and _________lookupoNotoLookupoLookupo y1159 y1160 y1161 y1162 y1163 y1164 y1165 =
    fresh (x3176 x3175 x3177)
      ( y1159
      === pair y1160 !!true % x3177
      &&& __notoLookupoLookupo y1161 y1160 x3177 y1162 y1163 y1164 y1165
      ||| (y1159 === pair x3175 x3176 % x3177 &&& (____lookupoLookupoLookupo x3177 y1160 x3175 x3176 y1162 y1163 y1164 y1165 &&& __noto y1161)) )
  and logintoAndoLookupo y1166 y1167 y1168 y1169 y1170 y1171 y1172 =
    fresh
      (x3493 x3531 x3491 x3530 x3521 x3522 x3519 x3490 x3507 x3506 x3489)
      ( y1167 === ltrue () &&& (y1168 === !!true)
      &&& ( y1169 === !!false &&& (y1170 === !!false) &&& _lookupo y1166 y1171 y1172
          ||| (y1169 === !!true &&& (y1170 === !!true) &&& _lookupo y1166 y1171 y1172) )
      ||| ( y1167 === lfalse () &&& (y1168 === !!false)
          &&& ( y1169 === !!false &&& (y1170 === !!false) &&& _lookupo y1166 y1171 y1172
              ||| (y1169 === !!true &&& (y1170 === !!false) &&& _lookupo y1166 y1171 y1172) )
          ||| ( y1167 === var x3489
              &&& ( y1169 === !!false &&& (y1168 === !!false) &&& (y1170 === !!false)
                  &&& _________________________________________lookupoLookupo y1166 x3489 y1171 y1172
                  ||| ( y1169 === !!false &&& (y1168 === !!true) &&& (y1170 === !!false)
                      &&& __________________________________________lookupoLookupo y1166 x3489 y1171 y1172
                      ||| ( y1169 === !!true &&& (y1168 === !!false) &&& (y1170 === !!false)
                          &&& _________________________________________lookupoLookupo y1166 x3489 y1171 y1172
                          ||| ( y1169 === !!true &&& (y1168 === !!true) &&& (y1170 === !!true)
                              &&& __________________________________________lookupoLookupo y1166 x3489 y1171 y1172 ) ) ) )
              ||| ( y1167 === neg x3506
                  &&& (logintoLookupo y1166 x3506 x3507 y1171 y1172 &&& (ando y1169 y1168 y1170 &&& _noto x3507 y1168))
                  ||| ( y1167 === conj x3490 x3519
                      &&& (logintoAndoLookupo y1166 x3519 x3522 x3521 y1168 y1171 y1172 &&& (_loginto y1166 x3519 x3522 &&& ando y1169 y1168 y1170))
                      ||| ( y1167 === disj x3530 x3491
                          &&& (logintoLookupo y1166 x3530 x3531 y1171 y1172 &&& (ando y1169 y1168 y1170 &&& logintoOro y1166 x3491 x3493 x3531 y1168)) ) ) ) )
          ) )
  and logintoLoginto y1173 y1174 y1175 y1176 y1177 =
    fresh
      (x3673 x3671 x3672 x3670 x3661 x3659 x3660 x3658 x3654 x3653 x3645 x3643 x3642 x3644 x3640 x3641 x3632)
      ( y1174 === ltrue () &&& (y1175 === !!true) &&& _loginto y1173 y1176 y1177
      ||| ( y1174 === lfalse () &&& (y1175 === !!false) &&& _loginto y1173 y1176 y1177
          ||| ( y1174 === var x3632
              &&& ( y1176 === ltrue () &&& (y1177 === !!true) &&& _lookupo y1173 x3632 y1175
                  ||| ( y1176 === lfalse () &&& (y1177 === !!false) &&& _lookupo y1173 x3632 y1175
                      ||| ( y1176 === var x3641 &&& _lookupoLookupo y1173 x3641 y1177 x3632 y1175
                          ||| ( y1176 === neg x3640
                              &&& logintoNotoLookupo y1173 x3640 x3644 y1177 x3632 y1175
                              ||| ( y1176 === conj x3642 x3643
                                  &&& logintoLogintoAndoLookupo y1173 x3642 x3644 x3643 x3645 y1177 x3632 y1175
                                  ||| (y1176 === disj x3642 x3643 &&& logintoLogintoOroLookupo y1173 x3642 x3644 x3643 x3645 y1177 x3632 y1175) ) ) ) ) )
              ||| ( y1174 === neg x3653
                  &&& (logintoLoginto y1173 x3653 x3654 y1176 y1177 &&& _noto x3654 y1175)
                  ||| ( y1174 === conj x3658 x3660
                      &&& (logintoLoginto y1173 x3658 x3659 x3660 x3661 &&& (ando x3659 x3661 y1175 &&& _loginto y1173 y1176 y1177))
                      ||| ( y1174 === disj x3670 x3672
                          &&& (logintoLoginto y1173 x3670 x3671 x3672 x3673 &&& (oro x3671 x3673 y1175 &&& _loginto y1173 y1176 y1177)) ) ) ) ) ) )
  and ___oro y1178 = y1178 === !!false ||| (y1178 === !!true)
  and ____oro y1179 = y1179 === !!true
  and _____oro y1180 y1181 =
    y1180 === !!false &&& (y1181 === !!true) ||| (y1180 === !!true &&& (y1181 === !!false) ||| (y1180 === !!true &&& (y1181 === !!true)))
  in
  loginto x0 x1
