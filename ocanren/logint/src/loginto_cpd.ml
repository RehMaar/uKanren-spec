open GT
open OCanren
open Std
open Nat

let topLevelCPD x0 x1 x2 =
  let rec loginto y0 y1 y2 =
    fresh (q1 q2 q3)
      ( y1 === lit y2
      ||| (y1 === var q1 &&& lookupo y0 y2 q1)
      ||| (y1 === neg q1 &&& logintoNoto y0 y2 q1)
      ||| (y1 === conj q2 q3 &&& logintoLogintoAndo y0 y2 q2 q3)
      ||| (y1 === disj q2 q3 &&& logintoLogintoOro y0 y2 q2 q3) )
  and lookupo y3 y4 y5 = fresh (q1 q2 q3) (y3 === pair y5 y4 % q1 ||| (y3 === pair q2 q3 % q1 &&& lookupo q1 y4 y5))
  and logintoNoto y6 y7 y8 =
    fresh (q1 q2 q3 q4)
      ( y8 === lit q1 &&& noto y7 q1
      ||| (y8 === var q2 &&& lookupoNoto y6 y7 q2)
      ||| (y8 === neg q2 &&& (logintoNoto y6 q1 q2 &&& noto y7 q1))
      ||| (y8 === conj q3 q4 &&& (logintoLogintoAndo y6 q1 q3 q4 &&& noto y7 q1))
      ||| (y8 === disj q3 q4 &&& (logintoLogintoOro y6 q1 q3 q4 &&& noto y7 q1)) )
  and noto y10 y11 = y11 === !!true &&& (y10 === !!false) ||| (y10 === !!true)
  and lookupoNoto y12 y13 y15 = fresh (q1 q2 q3 q4) (y12 === pair y15 q1 % q2 &&& noto y13 q1 ||| (y12 === pair q3 q4 % q2 &&& lookupoNoto q2 y13 y15))
  and logintoLogintoAndo y30 y31 y32 y33 =
    fresh (q1 q2 q3 q4 q5)
      ( y32 === lit q1
      &&& (loginto y30 y33 q2 &&& ando y31 q1 q2)
      ||| (y32 === var q3 &&& (lookupoAndo y30 y31 q2 q3 &&& loginto y30 y33 q2))
      ||| (y32 === neg q3 &&& (logintoNoto y30 q1 q3 &&& loginto y30 y33 q2 &&& ando y31 q1 q2))
      ||| (y32 === conj q4 q5 &&& (logintoLogintoAndo y30 q1 q4 q5 &&& loginto y30 y33 q2 &&& ando y31 q1 q2))
      ||| (y32 === disj q4 q5 &&& (logintoLogintoOro y30 q1 q4 q5 &&& loginto y30 y33 q2 &&& ando y31 q1 q2)) )
  and ando y36 y37 y38 = y37 === !!true &&& (y38 === !!true) &&& (y36 === !!true) ||| (y36 === !!false)
  and lookupoAndo y39 y40 y42 y43 =
    fresh (q1 q2 q3 q4) (y39 === pair y43 q1 % q2 &&& ando y40 q1 y42 ||| (y39 === pair q3 q4 % q2 &&& lookupoAndo q2 y40 y42 y43))
  and logintoLogintoOro y64 y65 y66 y67 =
    fresh (q1 q2 q3 q4 q5)
      ( y66 === lit q1
      &&& (loginto y64 y67 q2 &&& oro y65 q1 q2)
      ||| (y66 === var q3 &&& (lookupoOro y64 y65 q2 q3 &&& loginto y64 y67 q2))
      ||| (y66 === neg q3 &&& (logintoNoto y64 q1 q3 &&& loginto y64 y67 q2 &&& oro y65 q1 q2))
      ||| (y66 === conj q4 q5 &&& (logintoLogintoAndo y64 q1 q4 q5 &&& loginto y64 y67 q2 &&& oro y65 q1 q2))
      ||| (y66 === disj q4 q5 &&& (logintoLogintoOro y64 q1 q4 q5 &&& loginto y64 y67 q2 &&& oro y65 q1 q2)) )
  and oro y70 y71 y72 = y71 === !!true &&& (y70 === !!true) ||| (y72 === !!true &&& (y70 === !!true)) ||| (y70 === !!false)
  and lookupoOro y73 y74 y76 y77 =
    fresh (q1 q2 q3 q4) (y73 === pair y77 q1 % q2 &&& oro y74 q1 y76 ||| (y73 === pair q3 q4 % q2 &&& lookupoOro q2 y74 y76 y77))
  in
  loginto x0 x1 x2
