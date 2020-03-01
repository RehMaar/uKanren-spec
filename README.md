uKanren-spec
------------

## Общий метод суперкомпиляции


## Методы суперкомпиляции

Методы суперкомпиляции различаются тем, каким образом мы выбираем атом в конъюнкии,
который мы будем раскрывать.

* FU -- полный unfold.
На каждом шаге раскрываем все конънкты. 

* SU (sequential unfold) -- последовательный unfold.
Конъюнкию раскрываем последовательно. Для этого сохраняем индекс последнего раскрытого конъюнкта.

* RU (random unfold) -- случайный unfold.
На каждом шаге раскрываем случайный атом.

* NU (non recursive unfold) -- не рекурсивный unfold.
На каждом шаге сначала пытаемся раскрыть атом, в котором нет рекурсивного вызова,
если не получилось, то раскрываем атом с наименьшим определением.

* RecU (recursive unfold) -- рекурсивный unfold.
На каждом шаге сначала пытаемся раскрыть атом, в котором есть хоть один рекурсивный вызов,
если не получилось, то раскрываем атом с наименьшим определением.

* MinU (minimum unfold) -- минимальный unfold.
Сначала раскрываем конънкт с наименьшимопределением.

* MaxU (maximum unfold) -- максимальный unfold.
Сначала раскрываем конънкт с наибольшим определением.

## Размеры деревьев для запросов

**Depth** -- глубина дерева;
**Leafs** -- количество нод, которые являются вариантами промежуточных нод;
**Success** -- количество успешных нод;
**Fail** -- количество неудачных нод;
**Nodes** -- общее колчиество нод в дереве (включая промежуточные).

* Интерпретатор loginto subst formula для выполнимых формул.

Параметры дерева вывода

|Meth|Depth|Leafs|Success|Fail|Nodes|
|----|-----|-----|-------|----|----|
|RU  | 7 | 15 | 4 | 0 | 37|
|NU  | 7 | 15 | 4 | 0 | 37|
|MinU| 7 | 15 | 4 | 0 | 37|
|MaxU| 14 | 294 | 50 | 20 | 706|
|SU  | 18 | 362 | 56 | 8 | 793|
|RecU| 15 | 221 | 46 | 12 | 537|

NB: FU вычисляется слишком долго!

**Время генерации формул в подстановках**

* В пустой подстановке

| Meth| Time |
|-----|------|
|Orig | 0.280411|
|CPD  | 3.3303|
|NU   | 0.070193|
|SU   | 0.281896|
|MaxU | 0.19261|
|MinU | 0.0645345|
|RecU | 0.453004|
|RandU| 0.0778935|

* В подстановке с одной свбодной переменной

| Meth| Time|
|-----|------|
|Orig | 0.194816|
|CPD  | 1.89347|
|NU   | 0.0508587|
|SU   | 0.150367|
|MaxU | 0.136046|
|MinU | 0.0463975|
|RecU | 0.108195|
|RandU| 0.045203|


* Поиск всех путей графа: isPath q b

|Meth|Depth|Leafs|Success|Fail|Nodes|
|----|-----|-----|-------|----|----|
|RU  | 8 | 11 | 5 | 0 | 29|
|NU  | 8 | 9 | 8 | 0 | 31|
|MinU| 8 | 9 | 8 | 0 | 31|
|MaxU| 8 | 9 | 8 | 0 | 31|
|SU  | 8 | 9 | 8 | 0 | 31|
|RecU| 8 | 9 | 8 | 0 | 31|
|FU  | 8 | 15 | 17 | 0 | 46|

**Время запроса на графе K_10**

1. 100 путей.

|Meth|Time|
|----|----|
|Orig|1.36579|
|CPD |0.308703|
|FU  |0.980962|
|SU  |0.450304|
|MaxU|0.464006|
|MinU|0.466736|
|RecU|0.442815|
|NrcU|0.447074|


2. 500 путей.

|Meth|Time|
|---|---|
|Orig|15.673|
|CPD |3.09754|
|FU  |9.2531|
|SU  |4.07113|
|MaxU|3.90301|
|MinU|4.15037|
|RecU|4.01242|
|NrcU|3.90277|

3. 1000 путей.

|Meth|Time|
|---|---|
|Orig| 38.3305|
|CPD | 7.43097|
|FU  | 21.5917|
|SU  | 9.4462|
|MaxU| 9.50137|
|MinU| 9.32021|
|RecU| 9.25381|
|NrcU| 9.12053|

* Поиск путей фиксированной длины на K10.

   * Длины 5	

|Orig| 0.0229808|
|CPD | 0.0112195|
|FU  | 0.0104194|
|SU  | 0.0069789|
|MaxU| 0.007186|
|MinU| 0.0069818|
|RecU| 0.0075316|
|NrcU| 0.0067391|

   * Длины 7	
 
| Orig| 0.09783|
| CPD | 0.0555753|
| FU  | 0.0150126|
| SU  | 0.0111468|
| MaxU| 0.0099866|
| MinU| 0.010345|
| RecU| 0.0107588|
| NrcU| 0.010218|

   * Длины 9	

|Orig| 0.6061448|
|CPD | 0.3659386|
|FU  | 0.0214601|
|SU  | 0.0140709|
|MaxU| 0.0142263|
|MinU| 0.0143402|
|RecU| 0.0181662|
|NrcU| 0.0140454|

   * Длины 11	

|Orig| 3.9784958|
|CPD | 2.2680892|
|FU  | 0.0327629|
|SU  | 0.0185929|
|MaxU| 0.0183193|
|MinU| 0.0191448|
|RecU| 0.018933|
|NrcU| 0.0190552|

   * Длины 13
 
|Orig| 22.7313791|
|CPD | 12.5496708|
|FU  | 0.0351577|
|SU  | 0.0221253|
|MaxU| 0.0220965|
|MinU| 0.0219285|
|RecU| 0.0218325|
|NrcU| 0.0219216|

    * Длины 15

|Orig| 120.4817778|
|CPD | 63.1236095|
|FU  | 0.0414038|
|SU  | 0.0267962|
|MaxU| 0.0267545|
|MinU| 0.026964|
|RecU| 0.0273398|
|NrcU| 0.0264273|


* Поиск максимального значения и длины списка

|Meth|Depth|Leafs|Success|Fail|Nodes|
|----|-----|-----|-------|----|----|
|RU  | 13 | 10 | 8 | 0 | 45|
|NU  | 15 | 8 | 8 | 0 | 42|
|MinU| 15 | 8 | 8 | 0 | 42|
|MaxU| 15 | 8 | 8 | 0 | 44|
|SU  | 12 | 6 | 8 | 0 | 36|
|RecU| 15 | 8 | 8 | 0 | 44|
|FU  | 12 | 53 | 14 | 0 | 116|

* |[1..1]| = 10

|Meth|Time|
|---|---|
| Orig | 0.0001313|
| CPD  | 0.0000817|
| SU   | 0.013818|
| FU   | 0.0691585|
| MaxU | 0.0186781|
| MinU | 0.0131175|
| RandU| 0.0183716|
| RecU | 0.0136941|
| NRecU| 0.014956|

* |[1..10]| = 10

|Meth|Time|
|---|---|
|Orig | 0.0003318|
|CPD  | 0.0643878|
|SU   | 0.05914|
|FU   | 0.0448753|
|MaxU | 0.0560212|
|MinU | 0.0557889|
|RandU| 0.0563955|
|RecU | 0.0528089|
|NRecU| 0.0530054|

* |[1..10, 1..5]| = 15

 |Meth|Time|
 |---|---|
 |Orig | 0.0004071|
 |CPD  | 1.54952|
 |SU   | 2.62891|
 |FU   | 0.724321|
 |MaxU | 2.36509|
 |MinU | 2.49113|
 |RandU| 2.71401|
 |RecU | 2.4708|
 |NRecU| 2.45771|

* |[1..15]| = 15

|Meth|Time|
|---|---|
|Orig | 0.0006156|
|CPD  | 8.2799|
|SU   | 6.99648|
|FU   | 1.3886|
|MaxU | 6.97168|
|MinU | 7.19028|
|RandU| 7.74734|
|RecU | 7.15188|
|NRecU| 7.25149|
