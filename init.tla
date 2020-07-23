--------------------------------- MODULE init ---------------------------------
EXTENDS TLC, Integers, types
-------------------------------------------------------------------------------

VARIABLES S_active, O_func, O_data, O_na, S, Q

\* Переменные модели:
\* V \subseteq S_active x O_func x O_data x O_na
\*   - последовательность состояний реализации модели, где:
\* S_active - множество активных субъектов системы
\* O_func   - множество функционально ассоциированных с субъектами объектов
\* O_data   - множество ассоциированных с субъектами объектов-данных
\* O_na     - множество неассоциированных с субъектами объектов
\*
\* Q \subseteq S x O x E
\*   - последовательность запросов к системе в реализации
vars == <<S_active, O_func, O_data, O_na, S, Q>>

\* Модельные значение

\* Зарегистрированные субъекты системы
\* s0 - первоначальный системный субъект (ядро ОС)
s_0 ==      [sid        |-> 0,
             type       |-> "system",
             is_blocked |-> FALSE]

\* s_sorm - подсистема управления доступом
s_sorm ==   [sid        |-> 1,
             type       |-> "sorm",
             is_blocked |-> FALSE]

\* пользователь 1
s_2 ==      [sid        |-> 2,
             type       |-> "users",
             is_blocked |-> FALSE]
(*
\* пользователь 2
s_3 ==      [sid        |-> 3,
             type       |-> "users",
             is_blocked |-> FALSE]

\* системный субъект
s_4==      [sid        |-> 4,
             type       |-> "system",
             is_blocked |-> FALSE]
*)
\* Начальные объекты системы
\* o0 - процесс системного субъекта s0
o_0 ==       [oid        |-> 0,
             type       |-> "func",
             subj_assoc |-> {0},
             state      |-> RandomElement(1..ObjectStateMax)]

\* o_s - процесс s_sorm (аналог o_sorm' модели ИПСС)
o_s ==      [oid        |-> 1,
             type       |-> "func",
             subj_assoc |-> {1},
             state      |-> RandomElement(1..ObjectStateMax)]
(*
\* o_sorm - ассоциированный объект-данные s_sorm
o_sorm ==   [oid        |-> 2,
             type       |-> "data",
             subj_assoc |-> {1},
             state      |-> RandomElement(1..ObjectStateMax)]

\* неассоциированный объект
o_3 ==      [oid        |-> 3,
             type       |-> "na",
             subj_assoc |-> {},
             state      |-> RandomElement(1..ObjectStateMax)]
*)
===============================================================================
