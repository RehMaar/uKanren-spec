uKanren-spec
------------

## Общий метод суперкомпиляции


## Методы суперкомпиляции

Методы суперкомпиляции различаются тем, каким образом мы выбираем атом в конъюнкии,
который мы будем раскрывать.

* FU -- полный unfold
На каждом шаге раскрываем все конънкты. 

N.B.: Не рассматривается в статистике из-за того, что слишком долго считается.
      В ocanren вероятно будет stack overflow.

* SU (sequential unfold) -- последовательный unfold
Конъюнкию раскрываем последовательно. Для этого сохраняем индекс последнего раскрытого конъюнкта.

* RU (random unfold) -- случайный unfold
На каждом шаге раскрываем случайный атом.

* NU (non recursive unfold) -- не рекурсивный unfold
На каждом шаге сначала пытаемся раскрыть атом, в котором нет рекурсивного вызова,
если не получилось, то раскрываем атом с наименьшим определением.

* RecU (recursive unfold) -- рекурсивный unfold
На каждом шаге сначала пытаемся раскрыть атом, в котором есть хоть один рекурсивный вызов,
если не получилось, то раскрываем атом с наименьшим определением.

* MinU (minimum unfold) -- минимальный unfold
Сначала раскрываем конънкт с наименьшимопределением.

* MaxU (maximum unfold) -- максимальный unfold
Сначала раскрываем конънкт с наибольшим определением.

## Размеры деревьев для запросов

Depth -- глубина дерева;
Leafs -- количество нод, которые являются вариантами промежуточных нод.
Success -- количество успешных нод.
Fail -- количество неудачных нод.
Nodes -- общее колчиество нод в дереве (включая промежуточные).

* Интерпретатор loginto subst formula для выполнимых формул.

SU  : Depth: 11 Leafs: 154 Success: 48 Fail: 6  Nodes: 389
RU  : Depth: 7  Leafs: 15  Success: 4  Fail: 0  Nodes: 37
NU  : Depth: 7  Leafs: 15  Success: 4  Fail: 0  Nodes: 37
RecU: Depth: 12 Leafs: 123 Success: 46 Fail: 10 Nodes: 345
MinU: Depth: 7  Leafs: 15  Success: 4  Fail: 0  Nodes: 37
MaxU: Depth: 25 Leafs: 828 Success: 84 Fail: 30 Nodes: 1972

* Поиск всех путей графа: isPath q b

SU  : Depth: 8 Leafs: 9  Success: 8 Fail: 0 Nodes: 31
RU  : Depth: 8 Leafs: 11 Success: 5 Fail: 0 Nodes: 29
NU  : Depth: 8 Leafs: 9  Success: 8 Fail: 0 Nodes: 31
RecU: Depth: 8 Leafs: 9  Success: 8 Fail: 0 Nodes: 31
MinU: Depth: 8 Leafs: 9  Success: 8 Fail: 0 Nodes: 31
MaxU: Depth: 8 Leafs: 9  Success: 8 Fail: 0 Nodes: 31
