--------------------------------- MODULE ipes ---------------------------------
EXTENDS init
-------------------------------------------------------------------------------

\* EventD
\* Пустая операция
Event(arg) ==
        /\ UNCHANGED <<Requests>>
EventD ==
        \* Постусловия
        /\ Event(0)

-------------------------------------------------------------------------------

\* Type Invariant
\* Инвариант типов
TypeInv ==  /\ TRUE

-------------------------------------------------------------------------------

\* Init
\* Инициализация модели
Init == /\ Requests = {}

\* Next
\* Действия модели
Next ==
        \/ EventD

\* Spec
\* Спецификация модели
Spec == Init /\ [][Next]_vars

\* Invariants
\* Теорема, учитывающая инварианты: доказывается при верификации
THEOREM Spec => /\ []TypeInv

===============================================================================
