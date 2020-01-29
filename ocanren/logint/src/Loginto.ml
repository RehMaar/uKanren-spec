module L = List

open OCanren
open GT
open Std

open LogicExpr

let topLevelSU x0 =
  let rec loginto y0 =
    fresh
      (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40
         q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64)
      ( y0
      === pair (y ()) q1 % q2
      &&& ( q2
          === pair (x ()) !!true % q3
          &&& ( q1 === !!true &&& lookupo q3
              ||| (q3 === pair (y ()) !!true % q4 &&& __lookupo q4 ||| (q3 === pair q5 q6 % q7 &&& (lookupo (pair q5 q6 % q7) &&& ___lookupo q7))) )
          ||| ( q2
              === pair q8 q9 % q10
              &&& ( _lookupo q10
                  &&& ( pair q8 q9 % q10
                      === q11 &&& (q1 === !!true)
                      &&& __lookupo (pair q8 q9 % q10)
                      ||| (pair q8 q9 % q10 === q11 &&& lookupoLookupo q1 (pair q8 q9 % q10)) ) ) )
          ||| ( q2
              === pair (x ()) !!true % q12
              &&& ( _loginto q1 q12
                  ||| ( q12
                      === pair (y ()) q13 % q14
                      &&& ______lookupo q13 q14
                      ||| (q12 === pair q15 q16 % q17 &&& (_loginto q1 (pair q15 q16 % q17) &&& _______lookupo q17)) ) )
              ||| ( q2
                  === pair q18 q19 % q20
                  &&& ( _lookupo q20
                      &&& ( pair q18 q19 % q20
                          === q21
                          &&& ______lookupo q1 (pair q18 q19 % q20)
                          ||| (pair q18 q19 % q20 === q21 &&& _lookupoLookupo q1 (pair q18 q19 % q20)) ) ) )
              ||| ( q2
                  === pair (x ()) !!true % q22
                  &&& ( q1 === !!true &&& ____lookupo q22
                      ||| ( q22
                          === pair (y ()) !!true % q23
                          &&& ________lookupo q23
                          ||| (q22 === pair q24 q25 % q26 &&& (_loginto q1 (pair q24 q25 % q26) &&& ___lookupo q26)) ) )
                  ||| ( q2
                      === pair q27 q28 % q29
                      &&& ( _lookupo q29
                          &&& ( pair q27 q28 % q29
                              === q30 &&& (q1 === !!true)
                              &&& ________lookupo (pair q27 q28 % q29)
                              ||| (pair q27 q28 % q29 === q30 &&& __lookupoLookupo q1 (pair q27 q28 % q29)) ) ) ) ) ) )
      ||| (y0 === pair q31 q32 % q33 &&& (_lookupo (pair q31 q32 % q33) &&& (_______lookupo q33 &&& __loginto (pair q31 q32 % q33))))
      ||| ( y0
          === pair (y ()) !!true % q34
          &&& ( q34
              === pair (x ()) q35 % q36
              &&& ( ___loginto q35 q36
                  ||| ( q36
                      === pair (y ()) !!true % q37
                      &&& (q35 === !!true ||| __lookupo q37)
                      ||| (q36 === pair q38 q39 % q40 &&& (___loginto q35 (pair q38 q39 % q40) &&& ___lookupo q40)) ) )
              ||| (q34 === pair q41 q42 % q43 &&& (_____lookupo q43 &&& (__lookupo (pair q41 q42 % q43) &&& ____loginto (pair q41 q42 % q43))))
              ||| ( q34
                  === pair (x ()) q35 % q44
                  &&& ( _____loginto q35 q44
                      ||| ( q44
                          === pair (y ()) q45 % q46
                          &&& ______lookupo q45 q46
                          ||| (q44 === pair q47 q48 % q49 &&& (_____loginto q35 (pair q47 q48 % q49) &&& _______lookupo q49)) ) )
                  ||| ( q34
                      === pair q50 q51 % q52
                      &&& ( _____lookupo q52
                          &&& (______loginto (pair q50 q51 % q52) &&& (pair q50 q51 % q52 === q53 ||| (pair q50 q51 % q52 === q53 &&& _______lookupo q53))) )
                      )
                  ||| ( q34
                      === pair (x ()) q35 % q54
                      &&& ( _____loginto q35 q54
                          ||| ( q54
                              === pair (y ()) !!true % q55
                              &&& ________lookupo q55
                              ||| (q54 === pair q56 q57 % q58 &&& (_____loginto q35 (pair q56 q57 % q58) &&& ___lookupo q58)) ) )
                      ||| (q34 === pair q59 q60 % q61 &&& (_____lookupo q61 &&& (______loginto (pair q59 q60 % q61) &&& ____loginto (pair q59 q60 % q61)))) )
                  ) )
          ||| (y0 === pair q62 q63 % q64 &&& (_____lookupo (pair q62 q63 % q64) &&& (___lookupo q64 &&& __loginto (pair q62 q63 % q64)))) ) )
  and lookupo y1 = _lookupo y1
  and _lookupo y2 = fresh (q1 q2 q3) (y2 === pair (x ()) !!true % q1 ||| (y2 === pair q2 q3 % q1 &&& _lookupo q1))
  and __lookupo y3 = _lookupo y3
  and ___lookupo y4 = fresh (q1 q2 q3) (y4 === pair (y ()) !!true % q1 ||| (y4 === pair q2 q3 % q1 &&& ___lookupo q1))
  and lookupoLookupo y5 y6 = _lookupo y6 ||| lookupoLookupo y5 y6
  and _loginto y8 y9 = ____lookupo y9
  and ____lookupo y11 = _____lookupo y11
  and _____lookupo y13 = fresh (q1 q2 q3 q4) (y13 === pair (x ()) q1 % q2 ||| (y13 === pair q3 q4 % q2 &&& _____lookupo q2))
  and ______lookupo y15 y16 = _____lookupo y16
  and _______lookupo y18 = fresh (q1 q2 q3 q4) (y18 === pair (y ()) q1 % q2 ||| (y18 === pair q3 q4 % q2 &&& _______lookupo q2))
  and _lookupoLookupo y20 y21 = ______lookupo y20 y21 ||| _lookupoLookupo y20 y21
  and ________lookupo y25 = _____lookupo y25
  and __lookupoLookupo y27 y28 = ______lookupo y27 y28 ||| __lookupoLookupo y27 y28
  and __loginto y31 =
    fresh (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13)
      ( y31
      === pair (y ()) !!true % q1
      &&& __lookupo q1
      ||| (y31 === pair q2 q3 % q4 &&& (_lookupo (pair q2 q3 % q4) &&& ___lookupo q4))
      ||| ( y31
          === pair (y ()) q5 % q6
          &&& ______lookupo q5 q6
          ||| (y31 === pair q7 q8 % q9 &&& (_____lookupo (pair q7 q8 % q9) &&& _______lookupo q9))
          ||| (y31 === pair (y ()) !!true % q10 &&& ________lookupo q10 ||| (y31 === pair q11 q12 % q13 &&& (_____lookupo (pair q11 q12 % q13) &&& ___lookupo q13)))
          ) )
  and ___loginto y32 y33 = y32 === !!true ||| _lookupo y33
  and ____loginto y34 = ___lookupo y34
  and _____loginto y35 y36 = _____lookupo y36
  and ______loginto y38 = ________lookupo y38 in
  loginto x0

let runTestOnSubst query = L.iter (fun s -> Printf.printf "%s\n" @@ show(answer) (s#reify (Std.List.reify (Std.Pair.reify reify reify))))
		@@ RStream.take ~n:1 @@ query (fun i -> i)


let _ = runTestOnSubst @@ run q (fun q -> topLevelSU q) 
