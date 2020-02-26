open GT
open OCanren
open Std
open Nat
open LogicExpr
let sequLogint x0 x1 = let rec loginto y0 y1 = (fresh (x1422 x1421 x635 x1410 x633 x1409 x1314 x1313 x1307 x1305 x1306 x1304 x1298 x1296 x1297 x1295 x1282 x1281 x1274 x1273 x1271 x1275 x1270 x1245 x631 x623 x622 x209 x611 x207 x610 x505 x504 x498 x496 x497 x495 x407 x405 x406 x404 x393 x392 x254 x253 x251 x8 x255 x250 x215 x205 x6 x5 x197 x196 x22 x189 x20 x188 x7 x35 x34 x18 x3 x4) (((y1 === ltrue ()) ||| (((y1 === (var x4)) &&& (lookupo y0 x4)) ||| (((y1 === (neg x3)) &&& ((x3 === lfalse ()) ||| (((x3 === (var x18)) &&& (_lookupo y0 x18)) ||| (((x3 === (neg x34)) &&& ((_loginto y0 x34 x35) &&& ((_noto x7) &&& (noto x35 x7)))) ||| (((x3 === (conj x188 x20)) &&& ((_loginto y0 x188 x189) &&& ((_noto x7) &&& (logintoAndo y0 x20 x22 x189 x7)))) ||| ((x3 === (disj x196 x20)) &&& ((_loginto y0 x196 x197) &&& ((_noto x7) &&& (logintoOro y0 x20 x22 x197 x7))))))))) ||| (((y1 === (conj x5 x6)) &&& (((x5 === ltrue ()) &&& (loginto y0 x6)) ||| (((x5 === (var x205)) &&& (((x6 === ltrue ()) &&& (lookupoAndo y0 x205 x7)) ||| (((x6 === lfalse ()) &&& (_lookupoAndo y0 x205 x7)) ||| (((x6 === (var x215)) &&& (lookupoLookupo y0 x205 x215)) ||| (((x6 === (neg x250)) &&& ((((y0 === ((pair x205 !!true) % x255)) &&& ((x8 === !!true) &&& (__loginto x205 x255 x250 x251))) ||| ((y0 === ((pair x253 x254) % x392)) &&& (((x393 === ((pair x253 x254) % x392)) &&& (__lookupoAndo x392 x205 x7 x8)) &&& ((x393 === ((pair x253 x254) % x392)) &&& (_loginto x393 x250 x251))))) &&& (noto x251 x8))) ||| (((x6 === (conj x404 x406)) &&& ((logintoLoginto y0 x404 x405 x406 x407) &&& ((____ando x7 x8) &&& ((__lookupo y0 x205 x7) &&& (__ando x405 x407 x8))))) ||| ((x6 === (disj x495 x497)) &&& ((logintoLoginto y0 x495 x496 x497 x498) &&& ((____ando x7 x8) &&& ((__lookupo y0 x205 x7) &&& (__oro x496 x498 x8))))))))))) ||| (((x5 === (neg x504)) &&& ((logintoLogintoAndo y0 x504 x505 x6 x8 x7) &&& (noto x505 x7))) ||| (((x5 === (conj x610 x207)) &&& ((logintoLogintoAndo y0 x610 x611 x6 x8 x7) &&& ((__ando x611 x209 x7) &&& (_loginto y0 x6 x8)))) ||| ((x5 === (disj x622 x207)) &&& ((logintoLogintoAndo y0 x622 x623 x6 x8 x7) &&& ((__oro x623 x209 x7) &&& (_loginto y0 x6 x8))))))))) ||| ((y1 === (disj x5 x6)) &&& (((x5 === ltrue ()) &&& ((___loginto y0 x6) ||| (loginto y0 x6))) ||| (((x5 === lfalse ()) &&& (loginto y0 x6)) ||| (((x5 === (var x631)) &&& (((x6 === ltrue ()) &&& (_____lookupoOro y0 x631 x7)) ||| (((x6 === lfalse ()) &&& (______lookupoOro y0 x631 x7)) ||| (((x6 === (var x1245)) &&& ((___lookupoLookupo y0 x631 x1245) ||| ((____lookupoLookupo y0 x631 x1245) ||| (lookupoLookupo y0 x631 x1245)))) ||| (((x6 === (neg x1270)) &&& ((((y0 === ((pair x631 x7) % x1275)) &&& ((((x7 === !!false) &&& (x8 === !!true)) &&& (____loginto x631 x1275 x1270 x1271)) ||| ((((x7 === !!true) &&& (x8 === !!false)) &&& (__loginto x631 x1275 x1270 x1271)) ||| (((x7 === !!true) &&& (x8 === !!true)) &&& (__loginto x631 x1275 x1270 x1271))))) ||| ((y0 === ((pair x1273 x1274) % x1281)) &&& (((x1282 === ((pair x1273 x1274) % x1281)) &&& (_______lookupoOro x1281 x631 x7 x8)) &&& ((x1282 === ((pair x1273 x1274) % x1281)) &&& (_loginto x1282 x1270 x1271))))) &&& (noto x1271 x8))) ||| (((x6 === (conj x1295 x1297)) &&& ((logintoLoginto y0 x1295 x1296 x1297 x1298) &&& ((_______oro x7 x8) &&& ((__lookupo y0 x631 x7) &&& (__ando x1296 x1298 x8))))) ||| ((x6 === (disj x1304 x1306)) &&& ((logintoLoginto y0 x1304 x1305 x1306 x1307) &&& ((_______oro x7 x8) &&& ((__lookupo y0 x631 x7) &&& (__oro x1305 x1307 x8))))))))))) ||| (((x5 === (neg x1313)) &&& ((_logintoLogintoOro y0 x1313 x1314 x6 x8 x7) &&& (noto x1314 x7))) ||| (((x5 === (conj x1409 x633)) &&& ((_logintoLogintoOro y0 x1409 x1410 x6 x8 x7) &&& ((__ando x1410 x635 x7) &&& (_loginto y0 x6 x8)))) ||| ((x5 === (disj x1421 x633)) &&& ((_logintoLogintoOro y0 x1421 x1422 x6 x8 x7) &&& ((__oro x1422 x635 x7) &&& (_loginto y0 x6 x8)))))))))))))))) and lookupo y2 y3 = (fresh (x12 x11 x13) (((y2 === ((pair y3 !!true) % x13)) ||| ((y2 === ((pair x11 x12) % x13)) &&& (lookupo x13 y3))))) and _lookupo y4 y5 = (fresh (x29 x28 x30) (((y4 === ((pair y5 !!false) % x30)) ||| ((y4 === ((pair x28 x29) % x30)) &&& (_lookupo x30 y5))))) and _loginto y6 y7 y8 = (fresh (x179 x178 x42 x60 x40 x59 x53 x52 x38) ((((y7 === ltrue ()) &&& (y8 === !!true)) ||| (((y7 === lfalse ()) &&& (y8 === !!false)) ||| (((y7 === (var x38)) &&& (__lookupo y6 x38 y8)) ||| (((y7 === (neg x52)) &&& ((_loginto y6 x52 x53) &&& (noto x53 y8))) ||| (((y7 === (conj x59 x40)) &&& ((_loginto y6 x59 x60) &&& (logintoAndo y6 x40 x42 x60 y8))) ||| ((y7 === (disj x178 x40)) &&& ((_loginto y6 x178 x179) &&& (logintoOro y6 x40 x42 x179 y8)))))))))) and __lookupo y9 y10 y11 = (fresh (x47 x46 x48) (((y9 === ((pair y10 y11) % x48)) ||| ((y9 === ((pair x46 x47) % x48)) &&& (__lookupo x48 y10 y11))))) and noto y12 y13 = (((y12 === !!true) &&& (y13 === !!false)) ||| ((y12 === !!false) &&& (y13 === !!true))) and logintoAndo y14 y15 y16 y17 y18 = (fresh (x70 x112 x68 x111 x102 x103 x100 x67 x84 x83 x66) (((((y15 === ltrue ()) &&& (y16 === !!true)) &&& (ando y17 y18)) ||| ((((y15 === lfalse ()) &&& (y16 === !!false)) &&& (_ando y17 y18)) ||| (((y15 === (var x66)) &&& (((((y17 === !!false) &&& (y16 === !!false)) &&& (y18 === !!false)) &&& (_lookupo y14 x66)) ||| (((((y17 === !!false) &&& (y16 === !!true)) &&& (y18 === !!false)) &&& (lookupo y14 x66)) ||| (((((y17 === !!true) &&& (y16 === !!false)) &&& (y18 === !!false)) &&& (_lookupo y14 x66)) ||| ((((y17 === !!true) &&& (y16 === !!true)) &&& (y18 === !!true)) &&& (lookupo y14 x66)))))) ||| (((y15 === (neg x83)) &&& ((_loginto y14 x83 x84) &&& ((__ando y17 y16 y18) &&& (noto x84 y16)))) ||| (((y15 === (conj x67 x100)) &&& ((logintoAndo y14 x100 x103 x102 y16) &&& ((_loginto y14 x100 x103) &&& (__ando y17 y16 y18)))) ||| ((y15 === (disj x111 x68)) &&& ((_loginto y14 x111 x112) &&& ((__ando y17 y16 y18) &&& (logintoOro y14 x68 x70 x112 y16))))))))))) and ando y19 y20 = (((y19 === !!false) &&& (y20 === !!false)) ||| ((y19 === !!true) &&& (y20 === !!true))) and _ando y21 y22 = (((y21 === !!false) &&& (y22 === !!false)) ||| ((y21 === !!true) &&& (y22 === !!false))) and __ando y23 y24 y25 = ((((y23 === !!false) &&& (y24 === !!false)) &&& (y25 === !!false)) ||| ((((y23 === !!false) &&& (y24 === !!true)) &&& (y25 === !!false)) ||| ((((y23 === !!true) &&& (y24 === !!false)) &&& (y25 === !!false)) ||| (((y23 === !!true) &&& (y24 === !!true)) &&& (y25 === !!true))))) and logintoOro y26 y27 y28 y29 y30 = (fresh (x169 x170 x167 x153 x154 x151 x120 x137 x136 x119) (((((y27 === ltrue ()) &&& (y28 === !!true)) &&& (oro y29 y30)) ||| ((((y27 === lfalse ()) &&& (y28 === !!false)) &&& (_oro y29 y30)) ||| (((y27 === (var x119)) &&& (((((y29 === !!false) &&& (y28 === !!false)) &&& (y30 === !!false)) &&& (_lookupo y26 x119)) ||| (((((y29 === !!false) &&& (y28 === !!true)) &&& (y30 === !!true)) &&& (lookupo y26 x119)) ||| (((((y29 === !!true) &&& (y28 === !!false)) &&& (y30 === !!true)) &&& (_lookupo y26 x119)) ||| ((((y29 === !!true) &&& (y28 === !!true)) &&& (y30 === !!true)) &&& (lookupo y26 x119)))))) ||| (((y27 === (neg x136)) &&& ((_loginto y26 x136 x137) &&& ((__oro y29 y28 y30) &&& (noto x137 y28)))) ||| (((y27 === (conj x120 x151)) &&& ((logintoAndo y26 x151 x154 x153 y28) &&& ((_loginto y26 x151 x154) &&& (__oro y29 y28 y30)))) ||| ((y27 === (disj x120 x167)) &&& ((logintoOro y26 x167 x170 x169 y28) &&& ((_loginto y26 x167 x170) &&& (__oro y29 y28 y30))))))))))) and oro y31 y32 = (((y31 === !!false) &&& (y32 === !!true)) ||| ((y31 === !!true) &&& (y32 === !!true))) and _oro y33 y34 = (((y33 === !!false) &&& (y34 === !!false)) ||| ((y33 === !!true) &&& (y34 === !!true))) and __oro y35 y36 y37 = ((((y35 === !!false) &&& (y36 === !!false)) &&& (y37 === !!false)) ||| ((((y35 === !!false) &&& (y36 === !!true)) &&& (y37 === !!true)) ||| ((((y35 === !!true) &&& (y36 === !!false)) &&& (y37 === !!true)) ||| (((y35 === !!true) &&& (y36 === !!true)) &&& (y37 === !!true))))) and _noto y38 = (y38 === !!false) and lookupoAndo y39 y40 y41 = (fresh (x222 x221 x223) ((((y39 === ((pair y40 y41) % x223)) &&& (___ando y41)) ||| ((y39 === ((pair x221 x222) % x223)) &&& (lookupoAndo x223 y40 y41))))) and ___ando y42 = (y42 === !!true) and _lookupoAndo y43 y44 y45 = (fresh (x230 x229 x228) (((y43 === ((pair x228 x229) % x230)) &&& (_lookupoAndo x230 y44 y45)))) and lookupoLookupo y46 y47 y48 = (fresh (x246 x245 x236 x235 x237) ((((y46 === ((pair y47 !!true) % x237)) &&& (___lookupo y47 x237 y48)) ||| ((y46 === ((pair x235 x236) % x245)) &&& (((x246 === ((pair x235 x236) % x245)) &&& (lookupo x245 y47)) &&& ((x246 === ((pair x235 x236) % x245)) &&& (lookupo x246 y48))))))) and ___lookupo y49 y50 y51 = ((y51 === y49) ||| (lookupo y50 y51)) and __loginto y52 y53 y54 y55 = (fresh (x386 x385 x263 x279 x261 x278 x274 x273 x259) ((((y54 === ltrue ()) &&& (y55 === !!true)) ||| (((y54 === lfalse ()) &&& (y55 === !!false)) ||| (((y54 === (var x259)) &&& (((x259 === y52) &&& (y55 === !!true)) ||| (__lookupo y53 x259 y55))) ||| (((y54 === (neg x273)) &&& ((__loginto y52 y53 x273 x274) &&& (noto x274 y55))) ||| (((y54 === (conj x278 x261)) &&& ((__loginto y52 y53 x278 x279) &&& (_logintoAndo y52 y53 x261 x263 x279 y55))) ||| ((y54 === (disj x385 x261)) &&& ((__loginto y52 y53 x385 x386) &&& (_logintoOro y52 y53 x261 x263 x386 y55)))))))))) and _logintoAndo y56 y57 y58 y59 y60 y61 = (fresh (x289 x327 x287 x326 x317 x318 x315 x286 x303 x302 x285) (((((y58 === ltrue ()) &&& (y59 === !!true)) &&& (ando y60 y61)) ||| ((((y58 === lfalse ()) &&& (y59 === !!false)) &&& (_ando y60 y61)) ||| (((y58 === (var x285)) &&& (((((y60 === !!false) &&& (y59 === !!false)) &&& (y61 === !!false)) &&& (____lookupo y56 y57 x285)) ||| (((((y60 === !!false) &&& (y59 === !!true)) &&& (y61 === !!false)) &&& (___lookupo y56 y57 x285)) ||| (((((y60 === !!true) &&& (y59 === !!false)) &&& (y61 === !!false)) &&& (____lookupo y56 y57 x285)) ||| ((((y60 === !!true) &&& (y59 === !!true)) &&& (y61 === !!true)) &&& (___lookupo y56 y57 x285)))))) ||| (((y58 === (neg x302)) &&& ((__loginto y56 y57 x302 x303) &&& ((__ando y60 y59 y61) &&& (noto x303 y59)))) ||| (((y58 === (conj x286 x315)) &&& ((_logintoAndo y56 y57 x315 x318 x317 y59) &&& ((__loginto y56 y57 x315 x318) &&& (__ando y60 y59 y61)))) ||| ((y58 === (disj x326 x287)) &&& ((__loginto y56 y57 x326 x327) &&& ((__ando y60 y59 y61) &&& (_logintoOro y56 y57 x287 x289 x327 y59))))))))))) and ____lookupo y62 y63 y64 = (_lookupo y63 y64) and _logintoOro y65 y66 y67 y68 y69 y70 = (fresh (x376 x377 x374 x360 x361 x358 x335 x348 x347 x334) (((((y67 === ltrue ()) &&& (y68 === !!true)) &&& (oro y69 y70)) ||| ((((y67 === lfalse ()) &&& (y68 === !!false)) &&& (_oro y69 y70)) ||| (((y67 === (var x334)) &&& (((((y69 === !!false) &&& (y68 === !!false)) &&& (y70 === !!false)) &&& (____lookupo y65 y66 x334)) ||| (((((y69 === !!false) &&& (y68 === !!true)) &&& (y70 === !!true)) &&& (___lookupo y65 y66 x334)) ||| (((((y69 === !!true) &&& (y68 === !!false)) &&& (y70 === !!true)) &&& (____lookupo y65 y66 x334)) ||| ((((y69 === !!true) &&& (y68 === !!true)) &&& (y70 === !!true)) &&& (___lookupo y65 y66 x334)))))) ||| (((y67 === (neg x347)) &&& ((__loginto y65 y66 x347 x348) &&& ((__oro y69 y68 y70) &&& (noto x348 y68)))) ||| (((y67 === (conj x335 x358)) &&& ((_logintoAndo y65 y66 x358 x361 x360 y68) &&& ((__loginto y65 y66 x358 x361) &&& (__oro y69 y68 y70)))) ||| ((y67 === (disj x335 x374)) &&& ((_logintoOro y65 y66 x374 x377 x376 y68) &&& ((__loginto y65 y66 x374 x377) &&& (__oro y69 y68 y70))))))))))) and __lookupoAndo y71 y72 y73 y74 = (fresh (x396 x395 x397) ((((y71 === ((pair y72 y73) % x397)) &&& (____ando y73 y74)) ||| ((y71 === ((pair x395 x396) % x397)) &&& (__lookupoAndo x397 y72 y73 y74))))) and ____ando y75 y76 = ((y75 === !!true) &&& (y76 === !!true)) and logintoLoginto y77 y78 y79 y80 y81 = (fresh (x483 x481 x482 x480 x471 x469 x470 x468 x464 x463 x410) (((((y78 === ltrue ()) &&& (y79 === !!true)) &&& (_loginto y77 y80 y81)) ||| ((((y78 === lfalse ()) &&& (y79 === !!false)) &&& (_loginto y77 y80 y81)) ||| (((y78 === (var x410)) &&& (lookupoLoginto y77 x410 y79 y80 y81)) ||| (((y78 === (neg x463)) &&& ((logintoLoginto y77 x463 x464 y80 y81) &&& (noto x464 y79))) ||| (((y78 === (conj x468 x470)) &&& ((logintoLoginto y77 x468 x469 x470 x471) &&& ((__ando x469 x471 y79) &&& (_loginto y77 y80 y81)))) ||| ((y78 === (disj x480 x482)) &&& ((logintoLoginto y77 x480 x481 x482 x483) &&& ((__oro x481 x483 y79) &&& (_loginto y77 y80 y81))))))))))) and lookupoLoginto y82 y83 y84 y85 y86 = (fresh (x458 x456 x457 x455 x450 x448 x449 x447 x443 x442 x437 x438 x428 x427 x429 x419) (((((y85 === ltrue ()) &&& (y86 === !!true)) &&& (__lookupo y82 y83 y84)) ||| ((((y85 === lfalse ()) &&& (y86 === !!false)) &&& (__lookupo y82 y83 y84)) ||| (((y85 === (var x419)) &&& (((y82 === ((pair x419 y86) % x429)) &&& (((y83 === x419) &&& (y84 === y86)) ||| (__lookupo x429 y83 y84))) ||| ((y82 === ((pair x427 x428) % x438)) &&& (((x437 === ((pair x427 x428) % x438)) &&& (__lookupo x437 y83 y84)) &&& ((x437 === ((pair x427 x428) % x438)) &&& (__lookupo x438 x419 y86)))))) ||| (((y85 === (neg x442)) &&& ((lookupoLoginto y82 y83 y84 x442 x443) &&& (noto x443 y86))) ||| (((y85 === (conj x447 x449)) &&& ((logintoLoginto y82 x447 x448 x449 x450) &&& ((__lookupo y82 y83 y84) &&& (__ando x448 x450 y86)))) ||| ((y85 === (disj x455 x457)) &&& ((logintoLoginto y82 x455 x456 x457 x458) &&& ((__lookupo y82 y83 y84) &&& (__oro x456 x458 y86))))))))))) and logintoLogintoAndo y87 y88 y89 y90 y91 y92 = (fresh (x598 x597 x512 x586 x510 x585 x577 x576 x570 x568 x569 x567 x561 x559 x560 x558 x553 x552 x518 x508) (((((y88 === ltrue ()) &&& (y89 === !!true)) &&& (__logintoAndo y87 y90 y91 y92)) ||| ((((y88 === lfalse ()) &&& (y89 === !!false)) &&& (__logintoAndo y87 y90 y91 y92)) ||| (((y88 === (var x508)) &&& ((((y90 === ltrue ()) &&& (y91 === !!true)) &&& (___lookupoAndo y87 x508 y89 y92)) ||| ((((y90 === lfalse ()) &&& (y91 === !!false)) &&& (____lookupoAndo y87 x508 y89 y92)) ||| (((y90 === (var x518)) &&& (((y92 === !!true) &&& (y91 === !!true)) &&& (_lookupoLookupo y87 x508 y89 x518))) ||| (((y90 === (neg x552)) &&& ((lookupoLoginto y87 x508 y89 x552 x553) &&& ((____ando y92 y91) &&& (noto x553 y91)))) ||| (((y90 === (conj x558 x560)) &&& ((logintoLoginto y87 x558 x559 x560 x561) &&& ((____ando y92 y91) &&& ((__lookupo y87 x508 y89) &&& (__ando x559 x561 y91))))) ||| ((y90 === (disj x567 x569)) &&& ((logintoLoginto y87 x567 x568 x569 x570) &&& ((____ando y92 y91) &&& ((__lookupo y87 x508 y89) &&& (__oro x568 x570 y91))))))))))) ||| (((y88 === (neg x576)) &&& ((logintoLogintoAndo y87 x576 x577 y90 y91 y92) &&& (noto x577 y89))) ||| (((y88 === (conj x585 x510)) &&& ((logintoLogintoAndo y87 x585 x586 y90 y91 y92) &&& ((__ando x586 x512 y89) &&& (_loginto y87 y90 y91)))) ||| ((y88 === (disj x597 x510)) &&& ((logintoLogintoAndo y87 x597 x598 y90 y91 y92) &&& ((__oro x598 x512 y89) &&& (_loginto y87 y90 y91))))))))))) and __logintoAndo y93 y94 y95 y96 = (((y96 === !!true) &&& (y95 === !!true)) &&& (loginto y93 y94)) and ___lookupoAndo y97 y98 y99 y100 = (fresh (x525 x524 x526) ((((y97 === ((pair y98 y99) % x526)) &&& (___ando y100)) ||| ((y97 === ((pair x524 x525) % x526)) &&& (___lookupoAndo x526 y98 y99 y100))))) and ____lookupoAndo y101 y102 y103 y104 = (fresh (x532 x531 x530) (((y101 === ((pair x530 x531) % x532)) &&& (____lookupoAndo x532 y102 y103 y104)))) and _lookupoLookupo y105 y106 y107 y108 = (fresh (x548 x547 x538 x537 x539) ((((y105 === ((pair y106 y107) % x539)) &&& (((y108 === y106) &&& (y107 === !!true)) ||| (lookupo x539 y108))) ||| ((y105 === ((pair x537 x538) % x547)) &&& (((x548 === ((pair x537 x538) % x547)) &&& (__lookupo x547 y106 y107)) &&& ((x548 === ((pair x537 x538) % x547)) &&& (lookupo x548 y108))))))) and ___loginto y109 y110 = (fresh (x1234 x1233 x1063 x1222 x1061 x1221 x1130 x1129 x1123 x1121 x1122 x1120 x1114 x1112 x1113 x1111 x1100 x1099 x1094 x1093 x1091 x1095 x1090 x1069 x1059 x1051 x1050 x687 x1039 x685 x1038 x929 x928 x922 x920 x921 x919 x913 x911 x912 x910 x897 x896 x760 x759 x757 x643 x761 x756 x695 x683 x641 x640 x675 x674 x652 x667 x650 x666 x642 x660 x659 x648 x638 x639) (((y110 === lfalse ()) ||| (((y110 === (var x639)) &&& (_lookupo y109 x639)) ||| (((y110 === (neg x638)) &&& ((x638 === ltrue ()) ||| (((x638 === (var x648)) &&& (lookupo y109 x648)) ||| (((x638 === (neg x659)) &&& ((_loginto y109 x659 x660) &&& ((__noto x642) &&& (noto x660 x642)))) ||| (((x638 === (conj x666 x650)) &&& ((_loginto y109 x666 x667) &&& ((__noto x642) &&& (logintoAndo y109 x650 x652 x667 x642)))) ||| ((x638 === (disj x674 x650)) &&& ((_loginto y109 x674 x675) &&& ((__noto x642) &&& (logintoOro y109 x650 x652 x675 x642))))))))) ||| (((y110 === (conj x640 x641)) &&& (((x640 === ltrue ()) &&& (___loginto y109 x641)) ||| (((x640 === lfalse ()) &&& ((___loginto y109 x641) ||| (loginto y109 x641))) ||| (((x640 === (var x683)) &&& (((x641 === ltrue ()) &&& (_____lookupoAndo y109 x683 x642)) ||| (((x641 === lfalse ()) &&& (______lookupoAndo y109 x683 x642)) ||| (((x641 === (var x695)) &&& ((__lookupoLookupo y109 x683 x695) ||| ((___lookupoLookupo y109 x683 x695) ||| (____lookupoLookupo y109 x683 x695)))) ||| (((x641 === (neg x756)) &&& ((((y109 === ((pair x683 x642) % x761)) &&& ((((x642 === !!false) &&& (x643 === !!false)) &&& (____loginto x683 x761 x756 x757)) ||| ((((x642 === !!false) &&& (x643 === !!true)) &&& (____loginto x683 x761 x756 x757)) ||| (((x642 === !!true) &&& (x643 === !!false)) &&& (__loginto x683 x761 x756 x757))))) ||| ((y109 === ((pair x759 x760) % x896)) &&& (((x897 === ((pair x759 x760) % x896)) &&& (_______lookupoAndo x896 x683 x642 x643)) &&& ((x897 === ((pair x759 x760) % x896)) &&& (_loginto x897 x756 x757))))) &&& (noto x757 x643))) ||| (((x641 === (conj x910 x912)) &&& ((logintoLoginto y109 x910 x911 x912 x913) &&& ((_______ando x642 x643) &&& ((__lookupo y109 x683 x642) &&& (__ando x911 x913 x643))))) ||| ((x641 === (disj x919 x921)) &&& ((logintoLoginto y109 x919 x920 x921 x922) &&& ((_______ando x642 x643) &&& ((__lookupo y109 x683 x642) &&& (__oro x920 x922 x643))))))))))) ||| (((x640 === (neg x928)) &&& ((_logintoLogintoAndo y109 x928 x929 x641 x643 x642) &&& (noto x929 x642))) ||| (((x640 === (conj x1038 x685)) &&& ((_logintoLogintoAndo y109 x1038 x1039 x641 x643 x642) &&& ((__ando x1039 x687 x642) &&& (_loginto y109 x641 x643)))) ||| ((x640 === (disj x1050 x685)) &&& ((_logintoLogintoAndo y109 x1050 x1051 x641 x643 x642) &&& ((__oro x1051 x687 x642) &&& (_loginto y109 x641 x643)))))))))) ||| ((y110 === (disj x640 x641)) &&& (((x640 === lfalse ()) &&& (___loginto y109 x641)) ||| (((x640 === (var x1059)) &&& (((x641 === ltrue ()) &&& (lookupoOro y109 x1059 x642)) ||| (((x641 === lfalse ()) &&& (_lookupoOro y109 x1059 x642)) ||| (((x641 === (var x1069)) &&& (__lookupoLookupo y109 x1059 x1069)) ||| (((x641 === (neg x1090)) &&& ((((y109 === ((pair x1059 !!false) % x1095)) &&& ((x643 === !!false) &&& (____loginto x1059 x1095 x1090 x1091))) ||| ((y109 === ((pair x1093 x1094) % x1099)) &&& (((x1100 === ((pair x1093 x1094) % x1099)) &&& (__lookupoOro x1099 x1059 x642 x643)) &&& ((x1100 === ((pair x1093 x1094) % x1099)) &&& (_loginto x1100 x1090 x1091))))) &&& (noto x1091 x643))) ||| (((x641 === (conj x1111 x1113)) &&& ((logintoLoginto y109 x1111 x1112 x1113 x1114) &&& ((____oro x642 x643) &&& ((__lookupo y109 x1059 x642) &&& (__ando x1112 x1114 x643))))) ||| ((x641 === (disj x1120 x1122)) &&& ((logintoLoginto y109 x1120 x1121 x1122 x1123) &&& ((____oro x642 x643) &&& ((__lookupo y109 x1059 x642) &&& (__oro x1121 x1123 x643))))))))))) ||| (((x640 === (neg x1129)) &&& ((logintoLogintoOro y109 x1129 x1130 x641 x643 x642) &&& (noto x1130 x642))) ||| (((x640 === (conj x1221 x1061)) &&& ((logintoLogintoOro y109 x1221 x1222 x641 x643 x642) &&& ((__ando x1222 x1063 x642) &&& (_loginto y109 x641 x643)))) ||| ((x640 === (disj x1233 x1061)) &&& ((logintoLogintoOro y109 x1233 x1234 x641 x643 x642) &&& ((__oro x1234 x1063 x642) &&& (_loginto y109 x641 x643))))))))))))))) and __noto y111 = (y111 === !!true) and _____lookupoAndo y112 y113 y114 = (fresh (x702 x701 x703) ((((y112 === ((pair y113 y114) % x703)) &&& (_____ando y114)) ||| ((y112 === ((pair x701 x702) % x703)) &&& (_____lookupoAndo x703 y113 y114))))) and _____ando y115 = (y115 === !!false) and ______lookupoAndo y116 y117 y118 = (fresh (x709 x708 x710) ((((y116 === ((pair y117 y118) % x710)) &&& (______ando y118)) ||| ((y116 === ((pair x708 x709) % x710)) &&& (______lookupoAndo x710 y117 y118))))) and ______ando y119 = ((y119 === !!false) ||| (y119 === !!true)) and __lookupoLookupo y120 y121 y122 = (fresh (x728 x727 x718 x717 x719) ((((y120 === ((pair y121 !!false) % x719)) &&& (_____lookupo y121 x719 y122)) ||| ((y120 === ((pair x717 x718) % x727)) &&& (((x728 === ((pair x717 x718) % x727)) &&& (_lookupo x727 y121)) &&& ((x728 === ((pair x717 x718) % x727)) &&& (_lookupo x728 y122))))))) and _____lookupo y123 y124 y125 = ((y125 === y123) ||| (_lookupo y124 y125)) and ___lookupoLookupo y126 y127 y128 = (fresh (x742 x741 x733 x732 x734) ((((y126 === ((pair y127 !!false) % x734)) &&& (______lookupo y127 x734 y128)) ||| ((y126 === ((pair x732 x733) % x741)) &&& (((x742 === ((pair x732 x733) % x741)) &&& (_lookupo x741 y127)) &&& ((x742 === ((pair x732 x733) % x741)) &&& (lookupo x742 y128))))))) and ______lookupo y129 y130 y131 = (lookupo y130 y131) and ____lookupoLookupo y132 y133 y134 = (fresh (x752 x751 x747 x746 x748) ((((y132 === ((pair y133 !!true) % x748)) &&& (____lookupo y133 x748 y134)) ||| ((y132 === ((pair x746 x747) % x751)) &&& (((x752 === ((pair x746 x747) % x751)) &&& (lookupo x751 y133)) &&& ((x752 === ((pair x746 x747) % x751)) &&& (_lookupo x752 y134))))))) and ____loginto y135 y136 y137 y138 = (fresh (x888 x887 x769 x785 x767 x784 x780 x779 x765) ((((y137 === ltrue ()) &&& (y138 === !!true)) ||| (((y137 === lfalse ()) &&& (y138 === !!false)) ||| (((y137 === (var x765)) &&& (((x765 === y135) &&& (y138 === !!false)) ||| (__lookupo y136 x765 y138))) ||| (((y137 === (neg x779)) &&& ((____loginto y135 y136 x779 x780) &&& (noto x780 y138))) ||| (((y137 === (conj x784 x767)) &&& ((____loginto y135 y136 x784 x785) &&& (___logintoAndo y135 y136 x767 x769 x785 y138))) ||| ((y137 === (disj x887 x767)) &&& ((____loginto y135 y136 x887 x888) &&& (__logintoOro y135 y136 x767 x769 x888 y138)))))))))) and ___logintoAndo y139 y140 y141 y142 y143 y144 = (fresh (x795 x829 x793 x828 x819 x820 x817 x792 x805 x804 x791) (((((y141 === ltrue ()) &&& (y142 === !!true)) &&& (ando y143 y144)) ||| ((((y141 === lfalse ()) &&& (y142 === !!false)) &&& (_ando y143 y144)) ||| (((y141 === (var x791)) &&& (((((y143 === !!false) &&& (y142 === !!false)) &&& (y144 === !!false)) &&& (_____lookupo y139 y140 x791)) ||| (((((y143 === !!false) &&& (y142 === !!true)) &&& (y144 === !!false)) &&& (______lookupo y139 y140 x791)) ||| (((((y143 === !!true) &&& (y142 === !!false)) &&& (y144 === !!false)) &&& (_____lookupo y139 y140 x791)) ||| ((((y143 === !!true) &&& (y142 === !!true)) &&& (y144 === !!true)) &&& (______lookupo y139 y140 x791)))))) ||| (((y141 === (neg x804)) &&& ((____loginto y139 y140 x804 x805) &&& ((__ando y143 y142 y144) &&& (noto x805 y142)))) ||| (((y141 === (conj x792 x817)) &&& ((___logintoAndo y139 y140 x817 x820 x819 y142) &&& ((____loginto y139 y140 x817 x820) &&& (__ando y143 y142 y144)))) ||| ((y141 === (disj x828 x793)) &&& ((____loginto y139 y140 x828 x829) &&& ((__ando y143 y142 y144) &&& (__logintoOro y139 y140 x793 x795 x829 y142))))))))))) and __logintoOro y145 y146 y147 y148 y149 y150 = (fresh (x878 x879 x876 x862 x863 x860 x837 x850 x849 x836) (((((y147 === ltrue ()) &&& (y148 === !!true)) &&& (oro y149 y150)) ||| ((((y147 === lfalse ()) &&& (y148 === !!false)) &&& (_oro y149 y150)) ||| (((y147 === (var x836)) &&& (((((y149 === !!false) &&& (y148 === !!false)) &&& (y150 === !!false)) &&& (_____lookupo y145 y146 x836)) ||| (((((y149 === !!false) &&& (y148 === !!true)) &&& (y150 === !!true)) &&& (______lookupo y145 y146 x836)) ||| (((((y149 === !!true) &&& (y148 === !!false)) &&& (y150 === !!true)) &&& (_____lookupo y145 y146 x836)) ||| ((((y149 === !!true) &&& (y148 === !!true)) &&& (y150 === !!true)) &&& (______lookupo y145 y146 x836)))))) ||| (((y147 === (neg x849)) &&& ((____loginto y145 y146 x849 x850) &&& ((__oro y149 y148 y150) &&& (noto x850 y148)))) ||| (((y147 === (conj x837 x860)) &&& ((___logintoAndo y145 y146 x860 x863 x862 y148) &&& ((____loginto y145 y146 x860 x863) &&& (__oro y149 y148 y150)))) ||| ((y147 === (disj x837 x876)) &&& ((__logintoOro y145 y146 x876 x879 x878 y148) &&& ((____loginto y145 y146 x876 x879) &&& (__oro y149 y148 y150))))))))))) and _______lookupoAndo y151 y152 y153 y154 = (fresh (x900 x899 x901) ((((y151 === ((pair y152 y153) % x901)) &&& (_______ando y153 y154)) ||| ((y151 === ((pair x899 x900) % x901)) &&& (_______lookupoAndo x901 y152 y153 y154))))) and _______ando y155 y156 = (((y155 === !!false) &&& (y156 === !!false)) ||| (((y155 === !!false) &&& (y156 === !!true)) ||| ((y155 === !!true) &&& (y156 === !!false)))) and _logintoLogintoAndo y157 y158 y159 y160 y161 y162 = (fresh (x1026 x1025 x936 x1014 x934 x1013 x1005 x1004 x998 x996 x997 x995 x989 x987 x988 x986 x981 x980 x944 x932) (((((y158 === ltrue ()) &&& (y159 === !!true)) &&& (____logintoAndo y157 y160 y161 y162)) ||| ((((y158 === lfalse ()) &&& (y159 === !!false)) &&& (____logintoAndo y157 y160 y161 y162)) ||| (((y158 === (var x932)) &&& ((((y160 === ltrue ()) &&& (y161 === !!true)) &&& (________lookupoAndo y157 x932 y159 y162)) ||| ((((y160 === lfalse ()) &&& (y161 === !!false)) &&& (_________lookupoAndo y157 x932 y159 y162)) ||| (((y160 === (var x944)) &&& ((((y162 === !!false) &&& (y161 === !!false)) &&& (_____lookupoLookupo y157 x932 y159 x944)) ||| ((((y162 === !!false) &&& (y161 === !!true)) &&& (_lookupoLookupo y157 x932 y159 x944)) ||| (((y162 === !!true) &&& (y161 === !!false)) &&& (_____lookupoLookupo y157 x932 y159 x944))))) ||| (((y160 === (neg x980)) &&& ((lookupoLoginto y157 x932 y159 x980 x981) &&& ((_______ando y162 y161) &&& (noto x981 y161)))) ||| (((y160 === (conj x986 x988)) &&& ((logintoLoginto y157 x986 x987 x988 x989) &&& ((_______ando y162 y161) &&& ((__lookupo y157 x932 y159) &&& (__ando x987 x989 y161))))) ||| ((y160 === (disj x995 x997)) &&& ((logintoLoginto y157 x995 x996 x997 x998) &&& ((_______ando y162 y161) &&& ((__lookupo y157 x932 y159) &&& (__oro x996 x998 y161))))))))))) ||| (((y158 === (neg x1004)) &&& ((_logintoLogintoAndo y157 x1004 x1005 y160 y161 y162) &&& (noto x1005 y159))) ||| (((y158 === (conj x1013 x934)) &&& ((_logintoLogintoAndo y157 x1013 x1014 y160 y161 y162) &&& ((__ando x1014 x936 y159) &&& (_loginto y157 y160 y161)))) ||| ((y158 === (disj x1025 x934)) &&& ((_logintoLogintoAndo y157 x1025 x1026 y160 y161 y162) &&& ((__oro x1026 x936 y159) &&& (_loginto y157 y160 y161))))))))))) and ____logintoAndo y163 y164 y165 y166 = ((((y166 === !!false) &&& (y165 === !!false)) &&& (___loginto y163 y164)) ||| ((((y166 === !!false) &&& (y165 === !!true)) &&& (loginto y163 y164)) ||| (((y166 === !!true) &&& (y165 === !!false)) &&& (___loginto y163 y164)))) and ________lookupoAndo y167 y168 y169 y170 = (fresh (x951 x950 x952) ((((y167 === ((pair y168 y169) % x952)) &&& (_____ando y170)) ||| ((y167 === ((pair x950 x951) % x952)) &&& (________lookupoAndo x952 y168 y169 y170))))) and _________lookupoAndo y171 y172 y173 y174 = (fresh (x957 x956 x958) ((((y171 === ((pair y172 y173) % x958)) &&& (______ando y174)) ||| ((y171 === ((pair x956 x957) % x958)) &&& (_________lookupoAndo x958 y172 y173 y174))))) and _____lookupoLookupo y175 y176 y177 y178 = (fresh (x974 x973 x964 x963 x965) ((((y175 === ((pair y176 y177) % x965)) &&& (((y178 === y176) &&& (y177 === !!false)) ||| (_lookupo x965 y178))) ||| ((y175 === ((pair x963 x964) % x973)) &&& (((x974 === ((pair x963 x964) % x973)) &&& (__lookupo x973 y176 y177)) &&& ((x974 === ((pair x963 x964) % x973)) &&& (_lookupo x974 y178))))))) and lookupoOro y179 y180 y181 = (fresh (x1077 x1076 x1075) (((y179 === ((pair x1075 x1076) % x1077)) &&& (lookupoOro x1077 y180 y181)))) and _lookupoOro y182 y183 y184 = (fresh (x1082 x1081 x1083) ((((y182 === ((pair y183 y184) % x1083)) &&& (___oro y184)) ||| ((y182 === ((pair x1081 x1082) % x1083)) &&& (_lookupoOro x1083 y183 y184))))) and ___oro y185 = (y185 === !!false) and __lookupoOro y186 y187 y188 y189 = (fresh (x1103 x1102 x1104) ((((y186 === ((pair y187 y188) % x1104)) &&& (____oro y188 y189)) ||| ((y186 === ((pair x1102 x1103) % x1104)) &&& (__lookupoOro x1104 y187 y188 y189))))) and ____oro y190 y191 = ((y190 === !!false) &&& (y191 === !!false)) and logintoLogintoOro y192 y193 y194 y195 y196 y197 = (fresh (x1209 x1208 x1137 x1197 x1135 x1196 x1188 x1187 x1181 x1179 x1180 x1178 x1172 x1170 x1171 x1169 x1164 x1163 x1143 x1133) (((((y193 === ltrue ()) &&& (y194 === !!true)) &&& (___logintoOro y192 y195 y196 y197)) ||| ((((y193 === lfalse ()) &&& (y194 === !!false)) &&& (___logintoOro y192 y195 y196 y197)) ||| (((y193 === (var x1133)) &&& ((((y195 === ltrue ()) &&& (y196 === !!true)) &&& (___lookupoOro y192 x1133 y194 y197)) ||| ((((y195 === lfalse ()) &&& (y196 === !!false)) &&& (____lookupoOro y192 x1133 y194 y197)) ||| (((y195 === (var x1143)) &&& (((y197 === !!false) &&& (y196 === !!false)) &&& (_____lookupoLookupo y192 x1133 y194 x1143))) ||| (((y195 === (neg x1163)) &&& ((lookupoLoginto y192 x1133 y194 x1163 x1164) &&& ((____oro y197 y196) &&& (noto x1164 y196)))) ||| (((y195 === (conj x1169 x1171)) &&& ((logintoLoginto y192 x1169 x1170 x1171 x1172) &&& ((____oro y197 y196) &&& ((__lookupo y192 x1133 y194) &&& (__ando x1170 x1172 y196))))) ||| ((y195 === (disj x1178 x1180)) &&& ((logintoLoginto y192 x1178 x1179 x1180 x1181) &&& ((____oro y197 y196) &&& ((__lookupo y192 x1133 y194) &&& (__oro x1179 x1181 y196))))))))))) ||| (((y193 === (neg x1187)) &&& ((logintoLogintoOro y192 x1187 x1188 y195 y196 y197) &&& (noto x1188 y194))) ||| (((y193 === (conj x1196 x1135)) &&& ((logintoLogintoOro y192 x1196 x1197 y195 y196 y197) &&& ((__ando x1197 x1137 y194) &&& (_loginto y192 y195 y196)))) ||| ((y193 === (disj x1208 x1135)) &&& ((logintoLogintoOro y192 x1208 x1209 y195 y196 y197) &&& ((__oro x1209 x1137 y194) &&& (_loginto y192 y195 y196))))))))))) and ___logintoOro y198 y199 y200 y201 = (((y201 === !!false) &&& (y200 === !!false)) &&& (___loginto y198 y199)) and ___lookupoOro y202 y203 y204 y205 = (fresh (x1151 x1150 x1149) (((y202 === ((pair x1149 x1150) % x1151)) &&& (___lookupoOro x1151 y203 y204 y205)))) and ____lookupoOro y206 y207 y208 y209 = (fresh (x1156 x1155 x1157) ((((y206 === ((pair y207 y208) % x1157)) &&& (___oro y209)) ||| ((y206 === ((pair x1155 x1156) % x1157)) &&& (____lookupoOro x1157 y207 y208 y209))))) and _____lookupoOro y210 y211 y212 = (fresh (x1252 x1251 x1253) ((((y210 === ((pair y211 y212) % x1253)) &&& (_____oro y212)) ||| ((y210 === ((pair x1251 x1252) % x1253)) &&& (_____lookupoOro x1253 y211 y212))))) and _____oro y213 = ((y213 === !!false) ||| (y213 === !!true)) and ______lookupoOro y214 y215 y216 = (fresh (x1260 x1259 x1261) ((((y214 === ((pair y215 y216) % x1261)) &&& (______oro y216)) ||| ((y214 === ((pair x1259 x1260) % x1261)) &&& (______lookupoOro x1261 y215 y216))))) and ______oro y217 = (y217 === !!true) and _______lookupoOro y218 y219 y220 y221 = (fresh (x1285 x1284 x1286) ((((y218 === ((pair y219 y220) % x1286)) &&& (_______oro y220 y221)) ||| ((y218 === ((pair x1284 x1285) % x1286)) &&& (_______lookupoOro x1286 y219 y220 y221))))) and _______oro y222 y223 = (((y222 === !!false) &&& (y223 === !!true)) ||| (((y222 === !!true) &&& (y223 === !!false)) ||| ((y222 === !!true) &&& (y223 === !!true)))) and _logintoLogintoOro y224 y225 y226 y227 y228 y229 = (fresh (x1397 x1396 x1321 x1385 x1319 x1384 x1376 x1375 x1369 x1367 x1368 x1366 x1360 x1358 x1359 x1357 x1352 x1351 x1329 x1317) (((((y225 === ltrue ()) &&& (y226 === !!true)) &&& (____logintoOro y224 y227 y228 y229)) ||| ((((y225 === lfalse ()) &&& (y226 === !!false)) &&& (____logintoOro y224 y227 y228 y229)) ||| (((y225 === (var x1317)) &&& ((((y227 === ltrue ()) &&& (y228 === !!true)) &&& (________lookupoOro y224 x1317 y226 y229)) ||| ((((y227 === lfalse ()) &&& (y228 === !!false)) &&& (_________lookupoOro y224 x1317 y226 y229)) ||| (((y227 === (var x1329)) &&& ((((y229 === !!false) &&& (y228 === !!true)) &&& (_lookupoLookupo y224 x1317 y226 x1329)) ||| ((((y229 === !!true) &&& (y228 === !!false)) &&& (_____lookupoLookupo y224 x1317 y226 x1329)) ||| (((y229 === !!true) &&& (y228 === !!true)) &&& (_lookupoLookupo y224 x1317 y226 x1329))))) ||| (((y227 === (neg x1351)) &&& ((lookupoLoginto y224 x1317 y226 x1351 x1352) &&& ((_______oro y229 y228) &&& (noto x1352 y228)))) ||| (((y227 === (conj x1357 x1359)) &&& ((logintoLoginto y224 x1357 x1358 x1359 x1360) &&& ((_______oro y229 y228) &&& ((__lookupo y224 x1317 y226) &&& (__ando x1358 x1360 y228))))) ||| ((y227 === (disj x1366 x1368)) &&& ((logintoLoginto y224 x1366 x1367 x1368 x1369) &&& ((_______oro y229 y228) &&& ((__lookupo y224 x1317 y226) &&& (__oro x1367 x1369 y228))))))))))) ||| (((y225 === (neg x1375)) &&& ((_logintoLogintoOro y224 x1375 x1376 y227 y228 y229) &&& (noto x1376 y226))) ||| (((y225 === (conj x1384 x1319)) &&& ((_logintoLogintoOro y224 x1384 x1385 y227 y228 y229) &&& ((__ando x1385 x1321 y226) &&& (_loginto y224 y227 y228)))) ||| ((y225 === (disj x1396 x1319)) &&& ((_logintoLogintoOro y224 x1396 x1397 y227 y228 y229) &&& ((__oro x1397 x1321 y226) &&& (_loginto y224 y227 y228))))))))))) and ____logintoOro y230 y231 y232 y233 = ((((y233 === !!false) &&& (y232 === !!true)) &&& (loginto y230 y231)) ||| ((((y233 === !!true) &&& (y232 === !!false)) &&& (___loginto y230 y231)) ||| (((y233 === !!true) &&& (y232 === !!true)) &&& (loginto y230 y231)))) and ________lookupoOro y234 y235 y236 y237 = (fresh (x1336 x1335 x1337) ((((y234 === ((pair y235 y236) % x1337)) &&& (_____oro y237)) ||| ((y234 === ((pair x1335 x1336) % x1337)) &&& (________lookupoOro x1337 y235 y236 y237))))) and _________lookupoOro y238 y239 y240 y241 = (fresh (x1342 x1341 x1343) ((((y238 === ((pair y239 y240) % x1343)) &&& (______oro y241)) ||| ((y238 === ((pair x1341 x1342) % x1343)) &&& (_________lookupoOro x1343 y239 y240 y241))))) in                                                                          (loginto x0 x1)
