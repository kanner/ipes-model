--------------------------------- MODULE ipes ---------------------------------
EXTENDS init, types
-------------------------------------------------------------------------------

\* EventD
\* Пустая операция
Event(arg) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
EventD ==
        \* Постусловия
        /\ Event(0)

-------------------------------------------------------------------------------

\* Type Invariant
\* Инвариант типов
TypeInv == /\ S_active \subseteq Subjects
           /\ O_func \subseteq Objects
           /\ O_data \subseteq Objects
           /\ O_na \subseteq Objects
           /\ S \subseteq Subjects
           /\ O \subseteq Objects

-------------------------------------------------------------------------------

\* Init
\* Инициализация модели
Init == /\ S_active = {s0}
        /\ O_func = {o0}
        /\ O_data = {}
        /\ O_na = {}
        /\ S = {s0}
        /\ O = {o0}
        /\ Q = {}

\* Next
\* Действия модели
Next ==
        \/ EventD
(*
        \* Запросы к системе
        \/ CreateProcessD
        \/ DeleteProcessD
        \/ CreateUserD
        \/ CreateShadowD
        \/ DeleteSubjectD
        \/ ExecD
        \/ ReadD
        \/ WriteD
        \/ CreateD
        \/ DeleteD
        \* Административные действия
        \/ SormInit
        \/ SormBlockSubject
        \/ SormChangePerm
*)

\* Spec
\* Спецификация модели
Spec == Init /\ [][Next]_vars

\* Invariants
\* Теорема, учитывающая инварианты: доказывается при верификации
THEOREM Spec => /\ []TypeInv

===============================================================================
