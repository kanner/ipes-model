--------------------------------- MODULE ipes ---------------------------------
EXTENDS init, types
-------------------------------------------------------------------------------

\* CreateProcessD
\* Создание функционально ассоциированного объекта
CreateProcess(s,o,o_c) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
CreateProcessD ==
        \E s \in S:
        \E o \in O:
        \E o_c \in O:

            \* Постусловия
            /\ CreateProcess(s,o,o_c)

\* DeleteProcessD
\* Уничтожение функционально ассоциированного объекта
DeleteProcess(s,o,o_d) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
DeleteProcessD ==
        \E s \in S:
        \E o \in O:
        \E o_d \in O:

            \* Постусловия
            /\ DeleteProcess(s,o,o_d)

\* CreateUserD
\* Порождения субъекта-пользователя из объекта
CreateUser(s,o,s_u) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
CreateUserD ==
        \E s \in S:
        \E o \in O:
        \E s_u \in S:

            \* Постусловия
            /\ CreateUser(s,o,s_u)

\* CreateShadowD
\* Порождения системного субъекта из объекта
CreateShadow(s,o,s_w) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
CreateShadowD ==
        \E s \in S:
        \E o \in O:
        \E s_w \in S:

            \* Постусловия
            /\ CreateShadow(s,o,s_w)

\* DeleteSubjectD
\* Уничтожение всех функционально ассоциированных объектов
DeleteSubject(s,o,s_d) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
DeleteSubjectD ==
        \E s \in S:
        \E o \in O:
        \E s_d \in S:

            \* Постусловия
            /\ DeleteSubject(s,o,s_d)

\* ExecD
\* Загрузка бинарного образа для выполнения
Exec(s,o,o_e) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
ExecD ==
        \E s \in S:
        \E o \in O:
        \E o_e \in O:

            \* Постусловия
            /\ Exec(s,o,o_e)

\* ReadD
\* Реализация информационного потока на чтение
Read(s,o,o_r) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
ReadD ==
        \E s \in S:
        \E o \in O:
        \E o_r \in O:

            \* Постусловия
            /\ Read(s,o,o_r)

\* WriteD
\* Реализация информационного потока на запись
Write(s,o,o_w) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
WriteD ==
        \E s \in S:
        \E o \in O:
        \E o_w \in O:

            \* Постусловия
            /\ Write(s,o,o_w)

\* CreateD
\* Реализация информационного потока на создание объекта
Create(s,o,o_c) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
CreateD ==
        \E s \in S:
        \E o \in O:
        \E o_c \in O:

            \* Постусловия
            /\ Create(s,o,o_c)

\* DeleteD
\* Реализация информационного потока на удаление объекта
Delete(s,o,o_d) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
DeleteD ==
        \E s \in S:
        \E o \in O:
        \E o_d \in O:

            \* Постусловия
            /\ Delete(s,o,o_d)

-------------------------------------------------------------------------------

\* SormInitD
\* Инициализации подсистемы управления доступом
SormInit(s,o,o_sorm) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
SormInitD ==
        \E s \in S:
        \E o \in O:
        \E o_sorm \in O:

            \* Постусловия
            /\ SormInit(s,o,o_sorm)

\* SormBlockSubjectD
\* Изменение блокировки субъекта (разрешенный / неразрешенный)
SormBlockSubject(s,s_b) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
SormBlockSubjectD ==
        \E s \in S:
        \E s_b \in S:

            \* Постусловия
            /\ SormBlockSubject(s,s_b)

\* SormChangePermD
\* Изменение правил доступа
SormChangePerm(s,s_a,o_a) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, O, Q>>
SormChangePermD ==
        \E s \in S:
        \E s_a \in S:
        \E o_a \in O:

            \* Постусловия
            /\ SormChangePerm(s,s_a,o_a)

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
Init == /\ S_active = {s_0, s_sorm}
        /\ O_func = {o_0, o_s}
        /\ O_data = {} (*o_sorm*)
        /\ O_na = {}
        /\ O = {o0}
        /\ S = {s_2}
        /\ Q = {}

\* Next
\* Действия модели
Next ==
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
        \/ SormInitD
        \/ SormBlockSubjectD
        \/ SormChangePermD

\* Spec
\* Спецификация модели
Spec == Init /\ [][Next]_vars

\* Invariants
\* Теорема, учитывающая инварианты: доказывается при верификации
THEOREM Spec => /\ []TypeInv

===============================================================================
