open GT
open OCanren
open Std
open Nat
open LogicExpr
let fstuLogint x0 x1 = let rec loginto y0 y1 = (fresh (x970 x969 x634 x958 x632 x957 x831 x830 x821 x820 x717 x716 x814 x811 x815 x812 x813 x810 x803 x800 x804 x801 x802 x799 x748 x747 x721 x718 x630 x709 x708 x682 x701 x680 x700 x695 x694 x678 x670 x669 x641 x662 x639 x661 x656 x655 x637 x622 x621 x210 x610 x208 x609 x483 x482 x473 x472 x289 x288 x466 x463 x467 x464 x465 x462 x455 x452 x456 x453 x454 x451 x316 x315 x293 x290 x206 x281 x280 x256 x273 x254 x272 x267 x266 x252 x244 x243 x217 x236 x215 x235 x230 x229 x8 x213 x6 x5 x198 x197 x22 x190 x20 x189 x35 x34 x7 x18 x3 x4) (((y1 === ltrue ()) ||| (((y1 === (var x4)) &&& (lookupo y0 x4)) ||| (((y1 === (neg x3)) &&& ((x3 === lfalse ()) ||| (((x3 === (var x18)) &&& (lookupoNoto y0 x18 x7)) ||| (((x3 === (neg x34)) &&& ((_loginto y0 x34 x35) &&& ((noto x7) &&& (_noto x35 x7)))) ||| (((x3 === (conj x189 x20)) &&& ((_loginto y0 x189 x190) &&& ((noto x7) &&& (logintoAndo y0 x20 x22 x190 x7)))) ||| ((x3 === (disj x197 x20)) &&& ((_loginto y0 x197 x198) &&& ((noto x7) &&& (logintoOro y0 x20 x22 x198 x7))))))))) ||| (((y1 === (conj x5 x6)) &&& (((x5 === ltrue ()) &&& ((x6 === ltrue ()) ||| (((x6 === (var x213)) &&& (_lookupoAndo y0 x213 x8)) ||| (((x6 === (neg x229)) &&& ((_loginto y0 x229 x230) &&& ((_ando x8) &&& (_noto x230 x8)))) ||| (((x6 === (conj x235 x215)) &&& ((_loginto y0 x235 x236) &&& ((_ando x8) &&& (logintoAndo y0 x215 x217 x236 x8)))) ||| ((x6 === (disj x243 x215)) &&& ((_loginto y0 x243 x244) &&& ((_ando x8) &&& (logintoOro y0 x215 x217 x244 x8))))))))) ||| (((x5 === lfalse ()) &&& (((x6 === (var x252)) &&& (__lookupoAndo y0 x252 x8)) ||| (((x6 === (neg x266)) &&& ((_loginto y0 x266 x267) &&& (_noto x267 x8))) ||| (((x6 === (conj x272 x254)) &&& ((_loginto y0 x272 x273) &&& (logintoAndo y0 x254 x256 x273 x8))) ||| ((x6 === (disj x280 x254)) &&& ((_loginto y0 x280 x281) &&& (logintoOro y0 x254 x256 x281 x8))))))) ||| (((x5 === (var x206)) &&& (((y0 === ((pair x206 x7) % x290)) &&& (((x6 === ltrue ()) &&& (__ando x7)) ||| (((x6 === (var x293)) &&& ((((x293 === x206) &&& (x8 === x7)) &&& (x7 === !!true)) ||| (___lookupoAndo x290 x293 x8 x7))) ||| (((x6 === (neg x315)) &&& ((_logintoAndo x206 x7 x290 x315 x316 x8) &&& (_noto x316 x8))) ||| (((x6 === (conj x451 x454)) &&& ((((x453 === ((pair x206 x7) % x290)) &&& (x456 === x7)) &&& (logintoLoginto x453 x451 x452 x454 x455)) &&& ((((x453 === ((pair x206 x7) % x290)) &&& (x456 === x7)) &&& (___ando x456 x8)) &&& (ando x452 x455 x8)))) ||| ((x6 === (disj x462 x465)) &&& ((((x464 === ((pair x206 x7) % x290)) &&& (x467 === x7)) &&& (logintoLoginto x464 x462 x463 x465 x466)) &&& ((((x464 === ((pair x206 x7) % x290)) &&& (x467 === x7)) &&& (___ando x467 x8)) &&& (oro x463 x466 x8))))))))) ||| ((y0 === ((pair x288 x289) % x472)) &&& (((x473 === ((pair x288 x289) % x472)) &&& (_____lookupoAndo x472 x206 x7 x8)) &&& ((x473 === ((pair x288 x289) % x472)) &&& (_loginto x473 x6 x8)))))) ||| (((x5 === (neg x482)) &&& ((logintoLogintoAndo y0 x482 x483 x6 x8 x7) &&& (_noto x483 x7))) ||| (((x5 === (conj x609 x208)) &&& ((logintoLogintoAndo y0 x609 x610 x6 x8 x7) &&& ((ando x610 x210 x7) &&& (_loginto y0 x6 x8)))) ||| ((x5 === (disj x621 x208)) &&& ((logintoLogintoAndo y0 x621 x622 x6 x8 x7) &&& ((oro x622 x210 x7) &&& (_loginto y0 x6 x8)))))))))) ||| ((y1 === (disj x5 x6)) &&& (((x5 === ltrue ()) &&& ((x6 === ltrue ()) ||| ((x6 === lfalse ()) ||| (((x6 === (var x637)) &&& (_lookupoOro y0 x637 x8)) ||| (((x6 === (neg x655)) &&& ((_loginto y0 x655 x656) &&& ((_oro x8) &&& (_noto x656 x8)))) ||| (((x6 === (conj x661 x639)) &&& ((_loginto y0 x661 x662) &&& ((_oro x8) &&& (logintoAndo y0 x639 x641 x662 x8)))) ||| ((x6 === (disj x669 x639)) &&& ((_loginto y0 x669 x670) &&& ((_oro x8) &&& (logintoOro y0 x639 x641 x670 x8)))))))))) ||| (((x5 === lfalse ()) &&& ((x6 === ltrue ()) ||| (((x6 === (var x678)) &&& (__lookupoOro y0 x678 x8)) ||| (((x6 === (neg x694)) &&& ((_loginto y0 x694 x695) &&& ((__oro x8) &&& (_noto x695 x8)))) ||| (((x6 === (conj x700 x680)) &&& ((_loginto y0 x700 x701) &&& ((__oro x8) &&& (logintoAndo y0 x680 x682 x701 x8)))) ||| ((x6 === (disj x708 x680)) &&& ((_loginto y0 x708 x709) &&& ((__oro x8) &&& (logintoOro y0 x680 x682 x709 x8))))))))) ||| (((x5 === (var x630)) &&& (((y0 === ((pair x630 x7) % x718)) &&& (((x6 === ltrue ()) &&& (___oro x7)) ||| (((x6 === lfalse ()) &&& (____oro x7)) ||| (((x6 === (var x721)) &&& ((((x721 === x630) &&& (x8 === x7)) &&& (x7 === !!true)) ||| (___lookupoOro x718 x721 x8 x7))) ||| (((x6 === (neg x747)) &&& ((_logintoOro x630 x7 x718 x747 x748 x8) &&& (_noto x748 x8))) ||| (((x6 === (conj x799 x802)) &&& ((((x801 === ((pair x630 x7) % x718)) &&& (x804 === x7)) &&& (logintoLoginto x801 x799 x800 x802 x803)) &&& ((((x801 === ((pair x630 x7) % x718)) &&& (x804 === x7)) &&& (_____oro x804 x8)) &&& (ando x800 x803 x8)))) ||| ((x6 === (disj x810 x813)) &&& ((((x812 === ((pair x630 x7) % x718)) &&& (x815 === x7)) &&& (logintoLoginto x812 x810 x811 x813 x814)) &&& ((((x812 === ((pair x630 x7) % x718)) &&& (x815 === x7)) &&& (_____oro x815 x8)) &&& (oro x811 x814 x8)))))))))) ||| ((y0 === ((pair x716 x717) % x820)) &&& (((x821 === ((pair x716 x717) % x820)) &&& (_____lookupoOro x820 x630 x7 x8)) &&& ((x821 === ((pair x716 x717) % x820)) &&& (_loginto x821 x6 x8)))))) ||| (((x5 === (neg x830)) &&& ((logintoLogintoOro y0 x830 x831 x6 x8 x7) &&& (_noto x831 x7))) ||| (((x5 === (conj x957 x632)) &&& ((logintoLogintoOro y0 x957 x958 x6 x8 x7) &&& ((ando x958 x634 x7) &&& (_loginto y0 x6 x8)))) ||| ((x5 === (disj x969 x632)) &&& ((logintoLogintoOro y0 x969 x970 x6 x8 x7) &&& ((oro x970 x634 x7) &&& (_loginto y0 x6 x8)))))))))))))))) and lookupo y2 y3 = (fresh (x12 x11 x13) (((y2 === ((pair y3 !!true) % x13)) ||| ((y2 === ((pair x11 x12) % x13)) &&& (lookupo x13 y3))))) and lookupoNoto y4 y5 y6 = (fresh (x28 x27 x29) ((((y4 === ((pair y5 y6) % x29)) &&& (noto y6)) ||| ((y4 === ((pair x27 x28) % x29)) &&& (lookupoNoto x29 y5 y6))))) and noto y7 = (y7 === !!false) and _loginto y8 y9 y10 = (fresh (x181 x180 x42 x60 x40 x59 x53 x52 x38) ((((y9 === ltrue ()) &&& (y10 === !!true)) ||| (((y9 === lfalse ()) &&& (y10 === !!false)) ||| (((y9 === (var x38)) &&& (_lookupo y8 x38 y10)) ||| (((y9 === (neg x52)) &&& ((_loginto y8 x52 x53) &&& (_noto x53 y10))) ||| (((y9 === (conj x59 x40)) &&& ((_loginto y8 x59 x60) &&& (logintoAndo y8 x40 x42 x60 y10))) ||| ((y9 === (disj x180 x40)) &&& ((_loginto y8 x180 x181) &&& (logintoOro y8 x40 x42 x181 y10)))))))))) and _lookupo y11 y12 y13 = (fresh (x47 x46 x48) (((y11 === ((pair y12 y13) % x48)) ||| ((y11 === ((pair x46 x47) % x48)) &&& (_lookupo x48 y12 y13))))) and _noto y14 y15 = (((y14 === !!true) &&& (y15 === !!false)) ||| ((y14 === !!false) &&& (y15 === !!true))) and logintoAndo y16 y17 y18 y19 y20 = (fresh (x70 x113 x68 x112 x103 x104 x101 x67 x89 x88 x66) (((((y17 === ltrue ()) &&& (y18 === !!true)) &&& (((y19 === !!false) &&& (y20 === !!false)) ||| ((y19 === !!true) &&& (y20 === !!true)))) ||| ((((y17 === lfalse ()) &&& (y18 === !!false)) &&& (((y19 === !!false) &&& (y20 === !!false)) ||| ((y19 === !!true) &&& (y20 === !!false)))) ||| (((y17 === (var x66)) &&& (lookupoAndo y16 x66 y18 y19 y20)) ||| (((y17 === (neg x88)) &&& ((_loginto y16 x88 x89) &&& ((ando y19 y18 y20) &&& (_noto x89 y18)))) ||| (((y17 === (conj x67 x101)) &&& ((logintoAndo y16 x101 x104 x103 y18) &&& ((_loginto y16 x101 x104) &&& (ando y19 y18 y20)))) ||| ((y17 === (disj x112 x68)) &&& ((_loginto y16 x112 x113) &&& ((ando y19 y18 y20) &&& (logintoOro y16 x68 x70 x113 y18))))))))))) and lookupoAndo y21 y22 y23 y24 y25 = (fresh (x79 x78 x80) ((((y21 === ((pair y22 y23) % x80)) &&& (ando y24 y23 y25)) ||| ((y21 === ((pair x78 x79) % x80)) &&& (lookupoAndo x80 y22 y23 y24 y25))))) and ando y26 y27 y28 = ((((y26 === !!false) &&& (y27 === !!false)) &&& (y28 === !!false)) ||| ((((y26 === !!false) &&& (y27 === !!true)) &&& (y28 === !!false)) ||| ((((y26 === !!true) &&& (y27 === !!false)) &&& (y28 === !!false)) ||| (((y26 === !!true) &&& (y27 === !!true)) &&& (y28 === !!true))))) and logintoOro y29 y30 y31 y32 y33 = (fresh (x171 x172 x169 x155 x156 x153 x121 x143 x142 x120) (((((y30 === ltrue ()) &&& (y31 === !!true)) &&& (((y32 === !!false) &&& (y33 === !!true)) ||| ((y32 === !!true) &&& (y33 === !!true)))) ||| ((((y30 === lfalse ()) &&& (y31 === !!false)) &&& (((y32 === !!false) &&& (y33 === !!false)) ||| ((y32 === !!true) &&& (y33 === !!true)))) ||| (((y30 === (var x120)) &&& (lookupoOro y29 x120 y31 y32 y33)) ||| (((y30 === (neg x142)) &&& ((_loginto y29 x142 x143) &&& ((oro y32 y31 y33) &&& (_noto x143 y31)))) ||| (((y30 === (conj x121 x153)) &&& ((logintoAndo y29 x153 x156 x155 y31) &&& ((_loginto y29 x153 x156) &&& (oro y32 y31 y33)))) ||| ((y30 === (disj x121 x169)) &&& ((logintoOro y29 x169 x172 x171 y31) &&& ((_loginto y29 x169 x172) &&& (oro y32 y31 y33))))))))))) and lookupoOro y34 y35 y36 y37 y38 = (fresh (x133 x132 x134) ((((y34 === ((pair y35 y36) % x134)) &&& (oro y37 y36 y38)) ||| ((y34 === ((pair x132 x133) % x134)) &&& (lookupoOro x134 y35 y36 y37 y38))))) and oro y39 y40 y41 = ((((y39 === !!false) &&& (y40 === !!false)) &&& (y41 === !!false)) ||| ((((y39 === !!false) &&& (y40 === !!true)) &&& (y41 === !!true)) ||| ((((y39 === !!true) &&& (y40 === !!false)) &&& (y41 === !!true)) ||| (((y39 === !!true) &&& (y40 === !!true)) &&& (y41 === !!true))))) and _lookupoAndo y42 y43 y44 = (fresh (x223 x222 x224) ((((y42 === ((pair y43 y44) % x224)) &&& (_ando y44)) ||| ((y42 === ((pair x222 x223) % x224)) &&& (_lookupoAndo x224 y43 y44))))) and _ando y45 = (y45 === !!true) and __lookupoAndo y46 y47 y48 = (fresh (x262 x261 x260) (((y46 === ((pair x260 x261) % x262)) &&& (__lookupoAndo x262 y47 y48)))) and __ando y49 = (y49 === !!true) and ___lookupoAndo y50 y51 y52 y53 = (fresh (x309 x308 x310) ((((y50 === ((pair y51 y52) % x310)) &&& (___ando y53 y52)) ||| ((y50 === ((pair x308 x309) % x310)) &&& (___lookupoAndo x310 y51 y52 y53))))) and ___ando y54 y55 = ((y54 === !!true) &&& (y55 === !!true)) and _logintoAndo y56 y57 y58 y59 y60 y61 = (fresh (x443 x440 x441 x442 x439 x348 x345 x346 x347 x344 x339 x338 x319) (((((y59 === ltrue ()) &&& (y60 === !!true)) &&& (___ando y57 y61)) ||| ((((y59 === lfalse ()) &&& (y60 === !!false)) &&& (___ando y57 y61)) ||| (((y59 === (var x319)) &&& ((((x319 === y56) &&& (y60 === y57)) &&& (___ando y57 y61)) ||| (____lookupoAndo y58 x319 y60 y57 y61))) ||| (((y59 === (neg x338)) &&& ((_logintoAndo y56 y57 y58 x338 x339 y61) &&& (_noto x339 y60))) ||| (((y59 === (conj x344 x347)) &&& (((x346 === ((pair y56 y57) % y58)) &&& (logintoLoginto x346 x344 x345 x347 x348)) &&& (((x346 === ((pair y56 y57) % y58)) &&& (___ando y57 y61)) &&& (ando x345 x348 y60)))) ||| ((y59 === (disj x439 x442)) &&& (((x441 === ((pair y56 y57) % y58)) &&& (logintoLoginto x441 x439 x440 x442 x443)) &&& (((x441 === ((pair y56 y57) % y58)) &&& (___ando y57 y61)) &&& (oro x440 x443 y60))))))))))) and ____lookupoAndo y62 y63 y64 y65 y66 = (fresh (x333 x332 x334) ((((y62 === ((pair y63 y64) % x334)) &&& (___ando y65 y66)) ||| ((y62 === ((pair x332 x333) % x334)) &&& (____lookupoAndo x334 y63 y64 y65 y66))))) and logintoLoginto y67 y68 y69 y70 y71 = (fresh (x427 x425 x426 x424 x415 x413 x414 x412 x408 x407 x403 x402 x361 x360 x362 x352) (((((y68 === ltrue ()) &&& (y69 === !!true)) &&& (_loginto y67 y70 y71)) ||| ((((y68 === lfalse ()) &&& (y69 === !!false)) &&& (_loginto y67 y70 y71)) ||| (((y68 === (var x352)) &&& (((y67 === ((pair x352 y69) % x362)) &&& (__loginto x352 y69 x362 y70 y71)) ||| ((y67 === ((pair x360 x361) % x402)) &&& (((x403 === ((pair x360 x361) % x402)) &&& (_lookupo x402 x352 y69)) &&& ((x403 === ((pair x360 x361) % x402)) &&& (_loginto x403 y70 y71)))))) ||| (((y68 === (neg x407)) &&& ((logintoLoginto y67 x407 x408 y70 y71) &&& (_noto x408 y69))) ||| (((y68 === (conj x412 x414)) &&& ((logintoLoginto y67 x412 x413 x414 x415) &&& ((ando x413 x415 y69) &&& (_loginto y67 y70 y71)))) ||| ((y68 === (disj x424 x426)) &&& ((logintoLoginto y67 x424 x425 x426 x427) &&& ((oro x425 x427 y69) &&& (_loginto y67 y70 y71))))))))))) and __loginto y72 y73 y74 y75 y76 = (fresh (x398 x395 x396 x397 x394 x389 x386 x387 x388 x385 x380 x379 x365) ((((y75 === ltrue ()) &&& (y76 === !!true)) ||| (((y75 === lfalse ()) &&& (y76 === !!false)) ||| (((y75 === (var x365)) &&& (((x365 === y72) &&& (y76 === y73)) ||| (_lookupo y74 x365 y76))) ||| (((y75 === (neg x379)) &&& ((__loginto y72 y73 y74 x379 x380) &&& (_noto x380 y76))) ||| (((y75 === (conj x385 x388)) &&& (((x387 === ((pair y72 y73) % y74)) &&& (logintoLoginto x387 x385 x386 x388 x389)) &&& (ando x386 x389 y76))) ||| ((y75 === (disj x394 x397)) &&& (((x396 === ((pair y72 y73) % y74)) &&& (logintoLoginto x396 x394 x395 x397 x398)) &&& (oro x395 x398 y76)))))))))) and _____lookupoAndo y77 y78 y79 y80 = (fresh (x476 x475 x477) ((((y77 === ((pair y78 y79) % x477)) &&& (___ando y79 y80)) ||| ((y77 === ((pair x475 x476) % x477)) &&& (_____lookupoAndo x477 y78 y79 y80))))) and logintoLogintoAndo y81 y82 y83 y84 y85 y86 = (fresh (x597 x596 x490 x585 x488 x584 x576 x575 x571 x570 x526 x525 x565 x562 x563 x564 x561 x555 x552 x553 x554 x551 x545 x544 x530 x527 x486) (((((y82 === ltrue ()) &&& (y83 === !!true)) &&& (__logintoAndo y81 y84 y85 y86)) ||| ((((y82 === lfalse ()) &&& (y83 === !!false)) &&& (__logintoAndo y81 y84 y85 y86)) ||| (((y82 === (var x486)) &&& (((y81 === ((pair x486 y83) % x527)) &&& ((((y84 === ltrue ()) &&& (y85 === !!true)) &&& (__ando y86)) ||| (((y84 === (var x530)) &&& ((((x530 === x486) &&& (y85 === y83)) &&& (___ando y86 y83)) ||| (___lookupoAndo x527 x530 y85 y86))) ||| (((y84 === (neg x544)) &&& ((__loginto x486 y83 x527 x544 x545) &&& ((___ando y86 y85) &&& (_noto x545 y85)))) ||| (((y84 === (conj x551 x554)) &&& (((x553 === ((pair x486 y83) % x527)) &&& (logintoLoginto x553 x551 x552 x554 x555)) &&& (((x553 === ((pair x486 y83) % x527)) &&& (___ando y86 y85)) &&& (ando x552 x555 y85)))) ||| ((y84 === (disj x561 x564)) &&& (((x563 === ((pair x486 y83) % x527)) &&& (logintoLoginto x563 x561 x562 x564 x565)) &&& (((x563 === ((pair x486 y83) % x527)) &&& (___ando y86 y85)) &&& (oro x562 x565 y85))))))))) ||| ((y81 === ((pair x525 x526) % x570)) &&& (((x571 === ((pair x525 x526) % x570)) &&& (_lookupo x570 x486 y83)) &&& ((x571 === ((pair x525 x526) % x570)) &&& (__logintoAndo x571 y84 y85 y86)))))) ||| (((y82 === (neg x575)) &&& ((logintoLogintoAndo y81 x575 x576 y84 y85 y86) &&& (_noto x576 y83))) ||| (((y82 === (conj x584 x488)) &&& ((logintoLogintoAndo y81 x584 x585 y84 y85 y86) &&& ((ando x585 x490 y83) &&& (_loginto y81 y84 y85)))) ||| ((y82 === (disj x596 x488)) &&& ((logintoLogintoAndo y81 x596 x597 y84 y85 y86) &&& ((oro x597 x490 y83) &&& (_loginto y81 y84 y85))))))))))) and __logintoAndo y87 y88 y89 y90 = (fresh (x519 x517 x518 x516 x511 x509 x510 x508 x503 x502 x493) (((((y88 === ltrue ()) &&& (y89 === !!true)) &&& (__ando y90)) ||| (((y88 === (var x493)) &&& (___lookupoAndo y87 x493 y89 y90)) ||| (((y88 === (neg x502)) &&& ((_loginto y87 x502 x503) &&& ((___ando y90 y89) &&& (_noto x503 y89)))) ||| (((y88 === (conj x508 x510)) &&& ((logintoLoginto y87 x508 x509 x510 x511) &&& ((___ando y90 y89) &&& (ando x509 x511 y89)))) ||| ((y88 === (disj x516 x518)) &&& ((logintoLoginto y87 x516 x517 x518 x519) &&& ((___ando y90 y89) &&& (oro x517 x519 y89)))))))))) and _lookupoOro y91 y92 y93 = (fresh (x648 x647 x649) ((((y91 === ((pair y92 y93) % x649)) &&& (_oro y93)) ||| ((y91 === ((pair x647 x648) % x649)) &&& (_lookupoOro x649 y92 y93))))) and _oro y94 = ((y94 === !!false) ||| (y94 === !!true)) and __lookupoOro y95 y96 y97 = (fresh (x688 x687 x689) ((((y95 === ((pair y96 y97) % x689)) &&& (__oro y97)) ||| ((y95 === ((pair x687 x688) % x689)) &&& (__lookupoOro x689 y96 y97))))) and __oro y98 = (y98 === !!true) and ___oro y99 = ((y99 === !!false) ||| (y99 === !!true)) and ____oro y100 = (y100 === !!true) and ___lookupoOro y101 y102 y103 y104 = (fresh (x739 x738 x740) ((((y101 === ((pair y102 y103) % x740)) &&& (_____oro y104 y103)) ||| ((y101 === ((pair x738 x739) % x740)) &&& (___lookupoOro x740 y102 y103 y104))))) and _____oro y105 y106 = (((y105 === !!false) &&& (y106 === !!true)) ||| (((y105 === !!true) &&& (y106 === !!false)) ||| ((y105 === !!true) &&& (y106 === !!true)))) and _logintoOro y107 y108 y109 y110 y111 y112 = (fresh (x791 x788 x789 x790 x787 x780 x777 x778 x779 x776 x771 x770 x751) (((((y110 === ltrue ()) &&& (y111 === !!true)) &&& (_____oro y108 y112)) ||| ((((y110 === lfalse ()) &&& (y111 === !!false)) &&& (_____oro y108 y112)) ||| (((y110 === (var x751)) &&& ((((x751 === y107) &&& (y111 === y108)) &&& (_____oro y108 y112)) ||| (____lookupoOro y109 x751 y111 y108 y112))) ||| (((y110 === (neg x770)) &&& ((_logintoOro y107 y108 y109 x770 x771 y112) &&& (_noto x771 y111))) ||| (((y110 === (conj x776 x779)) &&& (((x778 === ((pair y107 y108) % y109)) &&& (logintoLoginto x778 x776 x777 x779 x780)) &&& (((x778 === ((pair y107 y108) % y109)) &&& (_____oro y108 y112)) &&& (ando x777 x780 y111)))) ||| ((y110 === (disj x787 x790)) &&& (((x789 === ((pair y107 y108) % y109)) &&& (logintoLoginto x789 x787 x788 x790 x791)) &&& (((x789 === ((pair y107 y108) % y109)) &&& (_____oro y108 y112)) &&& (oro x788 x791 y111))))))))))) and ____lookupoOro y113 y114 y115 y116 y117 = (fresh (x765 x764 x766) ((((y113 === ((pair y114 y115) % x766)) &&& (_____oro y116 y117)) ||| ((y113 === ((pair x764 x765) % x766)) &&& (____lookupoOro x766 y114 y115 y116 y117))))) and _____lookupoOro y118 y119 y120 y121 = (fresh (x824 x823 x825) ((((y118 === ((pair y119 y120) % x825)) &&& (_____oro y120 y121)) ||| ((y118 === ((pair x823 x824) % x825)) &&& (_____lookupoOro x825 y119 y120 y121))))) and logintoLogintoOro y122 y123 y124 y125 y126 y127 = (fresh (x945 x944 x838 x933 x836 x932 x924 x923 x919 x918 x874 x873 x913 x910 x911 x912 x909 x903 x900 x901 x902 x899 x893 x892 x878 x875 x834) (((((y123 === ltrue ()) &&& (y124 === !!true)) &&& (__logintoOro y122 y125 y126 y127)) ||| ((((y123 === lfalse ()) &&& (y124 === !!false)) &&& (__logintoOro y122 y125 y126 y127)) ||| (((y123 === (var x834)) &&& (((y122 === ((pair x834 y124) % x875)) &&& ((((y125 === ltrue ()) &&& (y126 === !!true)) &&& (___oro y127)) ||| ((((y125 === lfalse ()) &&& (y126 === !!false)) &&& (____oro y127)) ||| (((y125 === (var x878)) &&& ((((x878 === x834) &&& (y126 === y124)) &&& (_____oro y127 y124)) ||| (___lookupoOro x875 x878 y126 y127))) ||| (((y125 === (neg x892)) &&& ((__loginto x834 y124 x875 x892 x893) &&& ((_____oro y127 y126) &&& (_noto x893 y126)))) ||| (((y125 === (conj x899 x902)) &&& (((x901 === ((pair x834 y124) % x875)) &&& (logintoLoginto x901 x899 x900 x902 x903)) &&& (((x901 === ((pair x834 y124) % x875)) &&& (_____oro y127 y126)) &&& (ando x900 x903 y126)))) ||| ((y125 === (disj x909 x912)) &&& (((x911 === ((pair x834 y124) % x875)) &&& (logintoLoginto x911 x909 x910 x912 x913)) &&& (((x911 === ((pair x834 y124) % x875)) &&& (_____oro y127 y126)) &&& (oro x910 x913 y126)))))))))) ||| ((y122 === ((pair x873 x874) % x918)) &&& (((x919 === ((pair x873 x874) % x918)) &&& (_lookupo x918 x834 y124)) &&& ((x919 === ((pair x873 x874) % x918)) &&& (__logintoOro x919 y125 y126 y127)))))) ||| (((y123 === (neg x923)) &&& ((logintoLogintoOro y122 x923 x924 y125 y126 y127) &&& (_noto x924 y124))) ||| (((y123 === (conj x932 x836)) &&& ((logintoLogintoOro y122 x932 x933 y125 y126 y127) &&& ((ando x933 x838 y124) &&& (_loginto y122 y125 y126)))) ||| ((y123 === (disj x944 x836)) &&& ((logintoLogintoOro y122 x944 x945 y125 y126 y127) &&& ((oro x945 x838 y124) &&& (_loginto y122 y125 y126))))))))))) and __logintoOro y128 y129 y130 y131 = (fresh (x867 x865 x866 x864 x859 x857 x858 x856 x851 x850 x841) (((((y129 === ltrue ()) &&& (y130 === !!true)) &&& (___oro y131)) ||| ((((y129 === lfalse ()) &&& (y130 === !!false)) &&& (____oro y131)) ||| (((y129 === (var x841)) &&& (___lookupoOro y128 x841 y130 y131)) ||| (((y129 === (neg x850)) &&& ((_loginto y128 x850 x851) &&& ((_____oro y131 y130) &&& (_noto x851 y130)))) ||| (((y129 === (conj x856 x858)) &&& ((logintoLoginto y128 x856 x857 x858 x859) &&& ((_____oro y131 y130) &&& (ando x857 x859 y130)))) ||| ((y129 === (disj x864 x866)) &&& ((logintoLoginto y128 x864 x865 x866 x867) &&& ((_____oro y131 y130) &&& (oro x865 x867 y130))))))))))) in                                        (loginto x0 x1)
