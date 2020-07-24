--------------------------------- MODULE ipes ---------------------------------
EXTENDS init, types, select
-------------------------------------------------------------------------------

\* CreateProcessD
\* Создание функционально ассоциированного объекта
CreateProcess(s,o,x) ==
        /\ O_func' = O_func \cup {[oid |-> x,
                                   type |-> "func",
                                   subj_assoc |-> {s.sid},
                                   \* форк наследует состояние
                                   state |-> o.state]}
        /\ Q' = Q \cup {<<s.sid,o.oid,x,"create_process">>}
        /\ UNCHANGED <<S_active, O_data, O_na, S>>

CreateProcessD ==
        \* Активизирующее воздействие субъекта и его процесса
        \E s \in S_active:
        \E o \in SelectSubjProc(s):

        \E x \in ObjectIDs:

            \* Выбор свободного идентификатора
            /\ \A obj \in SelectObjects: obj.oid # x

            \* Постусловия
            /\ CreateProcess(s,o,x)

\* DeleteProcessD
\* Уничтожение функционально ассоциированного объекта
DeleteProcess(s,o) ==
        /\ O_func' = O_func \ {o}
        /\ Q' = Q \cup {<<s.sid,o.oid,o.oid,"delete_process">>}
        /\ UNCHANGED <<S_active, O_data, O_na, S>>

DeleteProcessD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):

            \* Нельзя удалять последний процесс -> DeleteSubjectD
            /\ Cardinality(SelectSubjProc(s)) > 1

            \* Постусловия
            /\ DeleteProcess(s,o)

\* CreateUserD
\* Порождения субъекта-пользователя из объекта
CreateUser(s,o,s_u) ==
        /\ S_active' = S_active \cup {s_u}
        /\ O_func' = (O_func \ {o}) \cup {[ o EXCEPT!["subj_assoc"]= {s_u.sid}]}
        /\ Q' = Q \cup {<<s.sid,o.oid,s_u.sid,"create_user">>}
        /\ UNCHANGED <<O_data, O_na, S>>

CreateUserD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E s_u \in S \ S_active: \* TODO: множество сессий?

            \* TODO: \/ s = s0
            \*       \/ s.type = "users"

            \* новый субъект типа "users"
            /\ s_u.type = "users"

            \* Нельзя порождать из последнего процесса
            /\ Cardinality(SelectSubjProc(s)) > 1

            \* Постусловия
            /\ CreateUser(s,o,s_u)

\* CreateShadowD
\* Порождения системного субъекта из объекта
CreateShadow(s,o,s_w) ==
        /\ S_active' = S_active \cup {s_w}
        /\ O_func' = (O_func \ {o}) \cup {[ o EXCEPT!["subj_assoc"]= {s_w.sid}]}
        /\ Q' = Q \cup {<<s.sid,o.oid,s_w.sid,"create_shadow">>}
        /\ UNCHANGED <<O_data, O_na, S>>

CreateShadowD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E s_w \in S \ S_active:

            \* порождение может выполнять только субъект s0
            /\ s.sid = s_0.sid

            \* новый субъект типа "system"
            /\ s_w.type = "system"

            \* Нельзя порождать из последнего процесса
            /\ Cardinality(SelectSubjProc(s)) > 1

            \* Постусловия
            /\ CreateShadow(s,o,s_w)

\* DeleteSubjectD
\* Уничтожение всех функционально ассоциированных объектов
DeleteSubject(s,o) ==
        \* для всех процессов выполняется DeleteProcess()
        /\ \A proc \in SelectSubjProc(s):
            /\ O_func' = O_func \ {proc}
            \* объекты-данные перестают быть ассоциированными
        /\  \/  /\ Cardinality(SelectSubjData(s)) > 0
                /\ \A d \in SelectSubjData(s):
                        \* неассоциированный объект должен перейти в O_na
                    /\  \/  /\ Cardinality(d.subj_assoc) = 1
                            /\ O_data' = O_data \ {d}
                            /\ O_na' = O_na \cup
                                {[ d EXCEPT!["subj_assoc"]=
                                    {}]}
                        \* из ассоциированных объектов исключается s.sid
                        \/  /\ Cardinality(d.subj_assoc) > 1
                            /\ O_data' = (O_data \ {d}) \cup
                                {[ d EXCEPT!["subj_assoc"]=
                                    (d.subj_assoc \ {s.sid})]}
                            /\ O_na' = O_na
            \/  /\ O_data' = O_data
                /\ O_na' = O_na
        /\ S_active' = S_active \ {s}
        /\ Q' = Q \cup {<<s.sid,o.oid,s.sid,"delete_subject">>}
        /\ UNCHANGED <<S>>

DeleteSubjectD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):

            \* s0, s_sorm не могут уничтожиться после активизации
            /\ s.sid # s_0.sid
            /\ s.sid # s_sorm.sid

            \* Постусловия
            /\ DeleteSubject(s,o)

\* ExecD
\* Загрузка бинарного образа для выполнения
Exec(s,o,o_e) ==
        \* бинарный файл загружается в процесс
        /\ O_func' = (O_func \ {o}) \cup
                {[ o EXCEPT!["state"]=
                    o_e.state]}
            \* объект перестает быть ассоциированным и переходит в O_na
        /\  \/  /\ Cardinality(o_e.subj_assoc) = 1
                /\ O_data' = O_data \ {o_e}
                /\ O_na' = O_na \cup
                    {[ o_e EXCEPT!["subj_assoc"]=
                        {}]}
            \* из ассоциированного объекта исключается s.sid
            \/  /\ Cardinality(o_e.subj_assoc) > 1
                /\ O_data' = (O_data \ {o_e}) \cup
                    {[ o_e EXCEPT!["subj_assoc"]=
                        (o_e.subj_assoc \ {s.sid})]}
                /\ O_na' = O_na
        /\ Q' = Q \cup {<<s.sid,o.oid,o_e.oid,"exec">>}
        /\ UNCHANGED <<S_active, S>>

ExecD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \* Объект уже прочитан
        \E o_e \in SelectSubjData(s):

            \* TODO: ПРД s_sorm

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
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, Q>>

WriteD ==
        \E s \in S:
        \E o \in SelectObjects:
        \E o_w \in SelectObjects:

            \* Постусловия
            /\ Write(s,o,o_w)

\* CreateD
\* Реализация информационного потока на создание объекта
Create(s,o,o_c) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, Q>>

CreateD ==
        \E s \in S:
        \E o \in SelectObjects:
        \E o_c \in SelectObjects:

            \* Постусловия
            /\ Create(s,o,o_c)

\* DeleteD
\* Реализация информационного потока на удаление объекта
Delete(s,o,o_d) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, Q>>

DeleteD ==
        \E s \in S:
        \E o \in SelectObjects:
        \E o_d \in SelectObjects:

            \* Постусловия
            /\ Delete(s,o,o_d)

-------------------------------------------------------------------------------

\* SormInitD
\* Инициализации подсистемы управления доступом
SormInit(s,o,o_n) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, Q>>

SormInitD ==
        \E s \in S:
        \E o \in SelectObjects:
        \E o_n \in SelectObjects:

            \* TODO - аналог CreateShadowD только для типа "sorm"

            \* Постусловия
            /\ SormInit(s,o,o_n(*o_sorm*))

\* SormBlockSubjectD
\* Изменение блокировки субъекта (разрешенный / неразрешенный)
SormBlockSubject(s,s_b) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, Q>>

SormBlockSubjectD ==
        \E s \in S:
        \E s_b \in S:

            \* Постусловия
            /\ SormBlockSubject(s,s_b)

\* SormChangePermD
\* Изменение правил доступа
SormChangePerm(s,s_a,o_a) ==
        /\ UNCHANGED <<S_active, O_func, O_data, O_na, S, Q>>

SormChangePermD ==
        \E s \in S:
        \E s_a \in S:
        \E o_a \in SelectObjects:

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

-------------------------------------------------------------------------------

\* Init
\* Инициализация модели
Init == /\ S_active = {s_0, s_sorm}
        /\ O_func = {o_0, o_s}
        /\ O_data = {} (*o_sorm*)
        /\ O_na = {}
        /\ S = {s_0, s_sorm, s_2, s_4}
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
