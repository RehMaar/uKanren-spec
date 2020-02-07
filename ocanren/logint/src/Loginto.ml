module L = List

open OCanren
open GT
open Std

open LogicExpr

(* Original interpreter *)
let loginto x0 x1 x2 =
   let rec loginto y0 y1 y2 = 
     fresh (rr rl r l y x) 
         ((((y1 === ltrue ()) &&& (y2 === !!true))
     ||| (((y1 === lfalse ()) &&& (y2 === !!false)) 
     ||| (((y1 === (var y)) &&& (lookupo y0 y y2))
     ||| (((y1 === (neg x)) &&& ((loginto y0 x rl) &&& (noto rl y2))) 
     ||| (((y1 === (conj l r)) &&& ((loginto y0 l rl) &&& ((loginto y0 r rr) &&& (ando rl rr y2))))
     ||| ((y1 === (disj l r)) &&& ((loginto y0 l rl) &&& ((loginto y0 r rr) &&& (oro rl rr y2))))))))))
  and lookupo y3 y4 y5 = 
     fresh (tail valu key) (((y3 === ((pair key valu) % tail)) &&& (((y4 === key) &&& (y5 === valu)) ||| (lookupo tail y4 y5))))
  and noto y6 y7 = 
     (((y6 === !!true) &&& (y7 === !!false)) ||| ((y6 === !!false) &&& (y7 === !!true))) 
  and ando y8 y9 y10 = 
     (((y8 === !!false) &&& ((y9 === !!false) &&& (y10 === !!false))) ||| (((y8 === !!false) &&& ((y9 === !!true) &&& (y10 === !!false))) ||| (((y8 === !!true) &&& ((y9 === !!false) &&& (y10 === !!false))) ||| ((y8 === !!true) &&& ((y9 === !!true) &&& (y10 === !!true)))))) 
  and oro y11 y12 y13 = 
     (((y11 === !!false) &&& ((y12 === !!false) &&& (y13 === !!false))) ||| (((y11 === !!false) &&& ((y12 === !!true) &&& (y13 === !!true))) ||| (((y11 === !!true) &&& ((y12 === !!false) &&& (y13 === !!true))) ||| ((y11 === !!true) &&& ((y12 === !!true) &&& (y13 === !!true))))))
  in loginto x0 x1 x2


(* CPD specialized version (on loginto X Y true). *)
let topLevel x0 x1 =
  let rec loginto y0 y1 =
    fresh (q1 q2 q3 q4 q5)
      ( y1 === ltrue ()
      ||| (y1 === var q5 &&& _lookupo !!true q5 y0)
      ||| (y1 === neg q1)
      ||| (y1 === conj q2 q3)
      ||| (y1 === disj q2 q3 &&& _logintoLogintoOro y0 q3 q4 q2 q4) )
  and logintoAndo y15 y16 y17 y18 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y17 === ltrue () &&& ando y16 y18 !!true
      ||| (y17 === lfalse () &&& ando y16 y18 !!false)
      ||| (y17 === var q6 &&& lookupoAndo y15 y16 y18 q6)
      ||| (y17 === neg q1 &&& (_loginto y15 q1 q2 &&& noto q3 q2 &&& ando y16 y18 q3))
      ||| (y17 === conj q4 q5 &&& (logintoAndo y15 q3 q5 q2 &&& _loginto y15 q4 q2 &&& ando y16 y18 q3))
      ||| (y17 === disj q4 q5 &&& (_logintoOro y15 q3 q5 q2 &&& _loginto y15 q4 q2 &&& ando y16 y18 q3)) )
  and lookupoAndo y20 y21 y22 y24 =
    fresh (q1 q2 q3 q4) (y20 === pair y24 q1 % q2 &&& ando y21 y22 q1 ||| (y20 === pair q3 q4 % q2 &&& lookupoAndo q2 y21 y22 y24))
  and _logintoOro y25 y26 y27 y28 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y27 === ltrue () &&& oro y26 y28 !!true
      ||| (y27 === lfalse () &&& oro y26 y28 !!false)
      ||| (y27 === var q6 &&& _lookupoOro y25 y26 y28 q6)
      ||| (y27 === neg q1 &&& (_loginto y25 q1 q2 &&& noto q3 q2 &&& oro y26 y28 q3))
      ||| (y27 === conj q4 q5 &&& (logintoAndo y25 q3 q5 q2 &&& _loginto y25 q4 q2 &&& oro y26 y28 q3))
      ||| (y27 === disj q4 q5 &&& (_logintoOro y25 q3 q5 q2 &&& _loginto y25 q4 q2 &&& oro y26 y28 q3)) )
  and _lookupoOro y30 y31 y32 y34 =
    fresh (q1 q2 q3 q4) (y30 === pair y34 q1 % q2 &&& oro y31 y32 q1 ||| (y30 === pair q3 q4 % q2 &&& _lookupoOro q2 y31 y32 y34))
  and __lookupoOro y41 y43 = fresh (q1 q2 q3 q4 q5) (y43 === pair q1 q2 % q3 &&& oro !!true q2 y41 ||| (y43 === pair q4 q5 % q3 &&& __lookupoOro y41 q3))
  and _logintoLogintoOro y44 y45 y46 y48 y49 =
    fresh (q1 q2 q3 q4 q5)
      ( y48 === ltrue () &&& (y49 === !!true) &&& _logintoOro y44 !!true y45 y46
      ||| (y48 === lfalse () &&& (y49 === !!false) &&& _logintoOro y44 !!true y45 y46)
      ||| (y48 === var q5 &&& _lookupoLogintoOro y44 y45 y46 y49 q5)
      ||| (y48 === neg q1 &&& (_logintoLogintoOro y44 y45 y46 q1 q2 &&& noto y49 q2))
      ||| (y48 === conj q3 q4 &&& (_logintoLogintoOro y44 y45 y46 q3 q2 &&& logintoAndo y44 y49 q4 q2))
      ||| (y48 === disj q3 q4 &&& (_logintoLogintoOro y44 y45 y46 q3 q2 &&& _logintoOro y44 y49 q4 q2)) )
  and _lookupoLogintoOro y50 y51 y52 y54 y55 =
    fresh (q1 q2 q3)
      ( y50
      === pair y55 y54 % q1
      &&& _logintoOro (pair y55 y54 % q1) !!true y51 y52
      ||| (y50 === pair q2 q3 % q1 &&& (_logintoOro (pair q2 q3 % q1) !!true y51 y52 &&& _lookupo y54 y55 q1)) )
  and _lookupo y56 y57 y58 = fresh (q1 q2 q3) (y58 === pair y57 y56 % q1 ||| (y58 === pair q2 q3 % q1 &&& _lookupo y56 y57 q1))
  and noto y59 y60 = y60 === !!true &&& (y59 === !!false) ||| (y60 === !!false &&& (y59 === !!true))
  and ando y61 y62 y63 =
    y62 === !!false &&& (y63 === !!false) &&& (y61 === !!false)
    ||| (y62 === !!false &&& (y63 === !!true) &&& (y61 === !!false))
    ||| (y62 === !!true &&& (y63 === !!false) &&& (y61 === !!false))
    ||| (y62 === !!true &&& (y63 === !!true) &&& (y61 === !!true))
  and _loginto y64 y65 y66 =
    fresh (q1 q2 q3 q4 q5)
      ( y65 === ltrue () &&& (y66 === !!true)
      ||| (y65 === lfalse () &&& (y66 === !!false))
      ||| (y65 === var q5 &&& _lookupo y66 q5 y64)
      ||| (y65 === neg q1 &&& (_loginto y64 q1 q2 &&& noto y66 q2))
      ||| (y65 === conj q3 q4 &&& (logintoAndo y64 y66 q4 q2 &&& _loginto y64 q3 q2))
      ||| (y65 === disj q3 q4 &&& (_logintoOro y64 y66 q4 q2 &&& _loginto y64 q3 q2)) )
  and oro y67 y68 y69 =
    y68 === !!false &&& (y69 === !!false) &&& (y67 === !!false)
    ||| (y68 === !!false &&& (y69 === !!true) &&& (y67 === !!true))
    ||| (y68 === !!true &&& (y69 === !!false) &&& (y67 === !!true))
    ||| (y68 === !!true &&& (y69 === !!true) &&& (y67 === !!true))
  in
  loginto x0 x1

(* NonRecUnfold specialized version. *)
let topLevelNU x0 x1 =
  let rec loginto y0 y1 =
    fresh (q1 q2 q3 q4)
      ( y1 === ltrue ()
      ||| ( y1 === var q4 &&& lookupo y0 q4
          ||| ( y1 === neg q1 &&& _loginto y0 q1
              ||| ( y1 === conj q2 q3 &&& ___logintoLoginto y0 q2 q3
                  ||| (y1 === disj q2 q3 &&& (_logintoLoginto y0 q2 q3 ||| (__logintoLoginto y0 q2 q3 ||| ___logintoLoginto y0 q2 q3))) ) ) ) )
  and lookupo y2 y3 = fresh (q1 q2 q3) (y2 === pair y3 !!true % q1 ||| (y2 === pair q2 q3 % q1 &&& lookupo q1 y3))
  and _loginto y4 y5 =
    fresh (q1 q2 q3 q4)
      ( y5 === lfalse ()
      ||| ( y5 === var q4 &&& _lookupo y4 q4
          ||| ( y5 === neg q1 &&& loginto y4 q1
              ||| ( y5 === conj q2 q3
                  &&& (logintoLoginto y4 q2 q3 ||| (_logintoLoginto y4 q2 q3 ||| __logintoLoginto y4 q2 q3))
                  ||| (y5 === disj q2 q3 &&& logintoLoginto y4 q2 q3) ) ) ) )
  and _lookupo y6 y7 = fresh (q1 q2 q3) (y6 === pair y7 !!false % q1 ||| (y6 === pair q2 q3 % q1 &&& _lookupo q1 y7))
  and logintoLoginto y8 y9 y10 = _loginto y8 y9 &&& _loginto y8 y10
  and _logintoLoginto y11 y12 y13 = loginto y11 y13 &&& _loginto y11 y12
  and __logintoLoginto y14 y15 y16 = loginto y14 y15 &&& _loginto y14 y16
  and ___logintoLoginto y17 y18 y19 = loginto y17 y18 &&& loginto y17 y19 in
  loginto x0 x1


let runTestOn x fn msg =
  let result = run q fn (fun i -> i) in
  let tx = Sys.time() in
  let answ = RStream.take ~n:x result in
  let t2 = Sys.time() in
  L.iter (fun s -> Printf.printf msg (t2 -. tx) @@ show(answer) (s#reify (Std.List.reify (Std.Pair.reify reify reify)))) answ;
  Printf.printf "\n%!"

let runTests x msg query = 
  Printf.printf "Formula: %s\n\n%!" msg;
  runTestOn x (fun q -> loginto q query !!true) ("Orig (%fs) >> %s\n%!");
  runTestOn x (fun q -> topLevel q query)       ("CPD (%fs) >> %s\n%!");
  runTestOn x (fun q -> topLevelNU q query)     ("NU  (%fs) >> %s\n%!")

let xVar = var (x ())
let yVar = var (y ())

(* (x \/ y) /\ (!x \/ !y) *)
let h1 = conj (disj xVar yVar) (disj (neg xVar) (neg yVar))

(* (x || y)(x || z)(!y || z)(!y || x)
 * Answ:
 *   - x = 1, y = 0, z = 1
 *   - x = 1, y = 1, z = 1
 *)
(*
let zVar = var (z ())
let h2 = conj (conj (conj (disj xVar yVar) (disj xVar zVar)) (disj (neg yVar) zVar)) (disj (neg yVar) xVar)
*)

let _ =
   runTests 2 "true" (ltrue ());
   runTests 2 "x" (var (x ()));
   (* CPD fails *)
   runTests 2 "!x" (neg (var (x ())));
   runTests 2 "!x \/ y" (disj (neg (var (x ()))) (var (y ())));
   (* CPD fails *)
   runTests 2 "!x /\ y" (conj (neg (var (x ()))) (var (y ())));
   (* CPD fails *)
   runTests 2 "(x \/ y)(!x \/ !y)" h1
(*
   (* CPD fails; original takes too long; NU gives wrong answer. *)
   runTests 2 "(x \/ y)(x \/ z)(!y \/ z)(!y \/ x)" h2
*)
