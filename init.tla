------------------------------- MODULE init -------------------------------
EXTENDS TLC, Integers, types
---------------------------------------------------------------------------

VARIABLES S_active, O_func, O_data, O_na, S, Q

\* Переменные модели:
\*
\* S - множество субъектов модели ИПСС
\*
\* V = S_active x O_func x O_data x O_na
\*   - множество всевозможных состояний модели, где:
\* S_active - множество активных субъектов системы
\* O_func   - множество функционально ассоциированных с субъектами объектов
\* O_data   - множество ассоциированных с субъектами объектов-данных
\* O_na     - множество неассоциированных с субъектами объектов
\*
\* Q = S x O x E
\*   - множество всевозможных запросов к системе
vars == <<S_active, O_func, O_data, O_na, S, Q>>

\* Модельные значение

\* Зарегистрированные субъекты системы
\* s_0 - первоначальный системный субъект (ядро ОС)
s_0 ==      [sid        |-> 0,
             type       |-> "system",
             is_blocked |-> FALSE]

\* s_sorm - подсистема управления доступом
s_sorm ==   [sid        |-> 1,
             type       |-> "sorm",
             is_blocked |-> FALSE]

\* пользователь
s_2 ==      [sid        |-> 2,
             type       |-> "users",
             is_blocked |-> FALSE]

\* системный субъект
s_3==       [sid        |-> 3,
             type       |-> "system",
             is_blocked |-> FALSE]

\* Начальные объекты системы
\* o_0 - процесс системного субъекта s_0
o_0 ==      [oid        |-> 0,
             type       |-> "func",
             subj_assoc |-> {0},
             state      |-> 0]

\* o_sorm - ассоциированный объект-данные s_sorm модели ИПСС
o_sorm ==   [oid        |-> 1,
             type       |-> "na",
             subj_assoc |-> {},
             state      |-> 1]

\* инициализирующий запрос
q_0 ==      [subj        |-> s_0,
             proc        |-> o_0,
             dent        |-> o_0,
             type        |-> "initial"]

===========================================================================
