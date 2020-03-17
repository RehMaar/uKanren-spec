open GT
open OCanren
open Std
open Nat

open LogicExpr

let rand1Loginto x0 x1 =
  let rec loginto y0 y1 =
    fresh (x6 x5 x12 x16 x15 x7 x10 x3 x4)
      ( y1 === ltrue ()
      ||| ( y1 === var x4 &&& lookupo y0 x4
          ||| ( y1 === neg x3
              &&& ( x3 === lfalse ()
                  ||| ( x3 === var x10 &&& lookupoNoto y0 x10 x7
                      ||| ( x3 === neg x15
                          &&& (_loginto y0 x15 x16 &&& (noto x7 &&& _noto x16 x7))
                          ||| ( x3 === conj x15 x12
                              &&& ( _loginto y0 x15 x16
                                  &&& ( noto x7
                                      &&& ( x16 === !!false &&& (x7 === !!false) &&& __loginto y0 x12
                                          ||| ( x16 === !!false &&& (x7 === !!false) &&& loginto y0 x12
                                              ||| ( x16 === !!true &&& (x7 === !!false) &&& __loginto y0 x12
                                                  ||| (x16 === !!true &&& (x7 === !!true) &&& loginto y0 x12) ) ) ) ) )
                              ||| ( x3 === disj x15 x12
                                  &&& ( _loginto y0 x15 x16
                                      &&& ( noto x7
                                          &&& ( x16 === !!false &&& (x7 === !!false) &&& __loginto y0 x12
                                              ||| ( x16 === !!false &&& (x7 === !!true) &&& loginto y0 x12
                                                  ||| ( x16 === !!true &&& (x7 === !!true) &&& __loginto y0 x12
                                                      ||| (x16 === !!true &&& (x7 === !!true) &&& loginto y0 x12) ) ) ) ) ) ) ) ) ) )
              ||| ( y1 === conj x5 x6 &&& ___logintoLoginto y0 x5 x6
                  ||| (y1 === disj x5 x6 &&& (_logintoLoginto y0 x5 x6 ||| (__logintoLoginto y0 x5 x6 ||| ___logintoLoginto y0 x5 x6))) ) ) ) )
  and lookupo y2 y3 = fresh (x10 x9 x11) (y2 === pair y3 !!true % x11 ||| (y2 === pair x9 x10 % x11 &&& lookupo x11 y3))
  and lookupoNoto y4 y5 y6 = fresh (x16 x15 x17) (y4 === pair y5 y6 % x17 &&& noto y6 ||| (y4 === pair x15 x16 % x17 &&& lookupoNoto x17 y5 y6))
  and noto y7 = y7 === !!false
  and _loginto y8 y9 y10 =
    fresh (x28 x27 x24 x23 x18)
      ( y9 === ltrue () &&& (y10 === !!true)
      ||| ( y9 === lfalse () &&& (y10 === !!false)
          ||| ( y9 === var x18 &&& _lookupo y8 x18 y10
              ||| ( y9 === neg x23
                  &&& (_loginto y8 x23 x24 &&& _noto x24 y10)
                  ||| ( y9 === conj x23 x27
                      &&& ( _loginto y8 x23 x24
                          &&& ( _loginto y8 x27 x28
                              &&& ( x24 === !!false &&& (x28 === !!false) &&& (y10 === !!false)
                                  ||| ( x24 === !!false &&& (x28 === !!true) &&& (y10 === !!false)
                                      ||| ( x24 === !!true &&& (x28 === !!false) &&& (y10 === !!false)
                                          ||| (x24 === !!true &&& (x28 === !!true) &&& (y10 === !!true)) ) ) ) ) )
                      ||| ( y9 === disj x23 x27
                          &&& ( _loginto y8 x23 x24
                              &&& ( _loginto y8 x27 x28
                                  &&& ( x24 === !!false &&& (x28 === !!false) &&& (y10 === !!false)
                                      ||| ( x24 === !!false &&& (x28 === !!true) &&& (y10 === !!true)
                                          ||| ( x24 === !!true &&& (x28 === !!false) &&& (y10 === !!true)
                                              ||| (x24 === !!true &&& (x28 === !!true) &&& (y10 === !!true)) ) ) ) ) ) ) ) ) ) ) )
  and _lookupo y11 y12 y13 = fresh (x24 x23 x25) (y11 === pair y12 y13 % x25 ||| (y11 === pair x23 x24 % x25 &&& _lookupo x25 y12 y13))
  and _noto y14 y15 = y14 === !!true &&& (y15 === !!false) ||| (y14 === !!false &&& (y15 === !!true))
  and __loginto y16 y17 =
    fresh (x22 x21 x19 x20)
      ( y17 === lfalse ()
      ||| ( y17 === var x20 &&& __lookupo y16 x20
          ||| ( y17 === neg x19 &&& loginto y16 x19
              ||| ( y17 === conj x21 x22
                  &&& (logintoLoginto y16 x21 x22 ||| (_logintoLoginto y16 x21 x22 ||| __logintoLoginto y16 x21 x22))
                  ||| (y17 === disj x21 x22 &&& logintoLoginto y16 x21 x22) ) ) ) )
  and __lookupo y18 y19 = fresh (x26 x25 x27) (y18 === pair y19 !!false % x27 ||| (y18 === pair x25 x26 % x27 &&& __lookupo x27 y19))
  and logintoLoginto y20 y21 y22 = __loginto y20 y21 &&& __loginto y20 y22
  and _logintoLoginto y23 y24 y25 = loginto y23 y25 &&& __loginto y23 y24
  and __logintoLoginto y26 y27 y28 = loginto y26 y27 &&& __loginto y26 y28
  and ___logintoLoginto y29 y30 y31 = loginto y29 y30 &&& loginto y29 y31 in
  loginto x0 x1
