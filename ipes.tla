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
        \E s_u \in SelectSubjAvail: \* TODO: множество сессий?

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
        \E s_w \in SelectSubjAvail:

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
                                {[oid |-> d.oid,
                                  type |-> "na",
                                  subj_assoc |-> {},
                                  state |-> d.state]}
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
                    {[oid |-> o_e.oid,
                      type |-> "na",
                      subj_assoc |-> {},
                      state |-> o_e.state]}
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
        \* процесс читает данные и изменяет свое состояние
        /\ O_func' = (O_func \ {o}) \cup
                {[ o EXCEPT!["state"]=
                    RandomElement(1..ObjectStateMax)]}
        \* объект с данными становится ассоциированным
        /\ O_data' = (O_data \ {o_r}) \cup
            {[oid |-> o_r.oid,
              type |-> "data",
              subj_assoc |-> (o_r.subj_assoc \cup {s.sid}),
              state |-> o_r.state]}
        /\ O_na' = O_na \ {o_r}
        /\ Q' = Q \cup {<<s.sid,o.oid,o_r.oid,"read">>}
        /\ UNCHANGED <<S_active, S>>

ReadD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E o_r \in SelectObjects \ O_func:

            \* процесс может читать если есть данные
            o_r.state # 0

            \* TODO: ПРД s_sorm

            \* Постусловия
            /\ Read(s,o,o_r)

\* WriteD
\* Реализация информационного потока на запись
Write(s,o,o_w) ==
        \* изменяется состояние объекта
        /\  \/  /\ o_w \in O_na
                /\ O_na' = (O_na \ {o_w}) \cup
                        {[ o_w EXCEPT!["state"]=
                            RandomElement(1..ObjectStateMax)]}
                /\ O_data' = O_data
            \/  /\ o_w \in O_data
                /\ O_data' = (O_data \ {o_w}) \cup
                        {[ o_w EXCEPT!["state"]=
                            RandomElement(1..ObjectStateMax)]}
                /\ O_na' = O_na
        /\ Q' = Q \cup {<<s.sid,o.oid,o_w.oid,"write">>}
        /\ UNCHANGED <<S_active, O_func, S>>

WriteD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E o_w \in SelectObjects \ O_func:

            \* TODO: ПРД s_sorm

            \* Постусловия
            /\ Write(s,o,o_w)

\* CreateD
\* Реализация информационного потока на создание объекта
Create(s,o,x) ==
        /\ O_na' = O_na \cup {[oid |-> x,
                               type |-> "na",
                               subj_assoc |-> {},
                               \* изначально состояние пустое
                               state |-> 0]}
        /\ Q' = Q \cup {<<s.sid,o.oid,x,"create">>}
        /\ UNCHANGED <<S_active, O_func, O_data, S>>

CreateD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):

        \E x \in ObjectIDs:

            \* Выбор свободного идентификатора
            /\ \A obj \in SelectObjects: obj.oid # x

            \* TODO: ПРД s_sorm

            \* Постусловия
            /\ Create(s,o,x)

\* DeleteD
\* Реализация информационного потока на удаление объекта
Delete(s,o,o_d) ==
        /\ O_na' = O_na \ {o_d}
        /\ O_data' = O_data \ {o_d}
        /\ Q' = Q \cup {<<s.sid,o.oid,o_d.oid,"delete">>}
        /\ UNCHANGED <<S_active, O_func, S>>

DeleteD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E o_d \in SelectObjects \ O_func:

            \* TODO: ПРД s_sorm

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
SormBlockSubject(s,o,s_b) ==
        /\ S' = (S \ {s_b}) \cup
            {[ s_b EXCEPT!["is_blocked"]= (\neg s_b.is_blocked) ]}
        /\ Q' = Q \cup {<<s.sid,o.oid,s_b.sid,"change_blocked">>}
        /\ UNCHANGED <<S_active, O_func, O_data, O_na>>

SormBlockSubjectD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \* для уменьшения возможных состояний блокировать можно
        \* только неактивного пользователя
        \E s_b \in S \ S_active:

            \* Административные действия выполняет только s_sorm
            /\ s.sid = s_sorm.sid

            \* блокировать s_0 или s_sorm нельзя
            /\ s_b.sid # s_0.sid
            /\ s_b.sid # s_sorm.sid

            \* Постусловия
            /\ SormBlockSubject(s,o,s_b)

-------------------------------------------------------------------------------

\* Type Invariant
\* Инвариант типов
TypeInv ==  /\ S_active \subseteq Subjects
            /\ O_func \subseteq Objects
            /\ O_data \subseteq Objects
            /\ O_na \subseteq Objects
            /\ S \subseteq Subjects

\* OSKernelExists
\* В любой момент времени существует s_0
OSKernelExists ==
            /\ s_0 \in S_active

\* SormExists
\* В любой момент времени существует s_sorm
SormExists ==
            /\ s_sorm \in S_active

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

\* Spec
\* Спецификация модели
Spec == Init /\ [][Next]_vars

\* Invariants
\* Теорема, учитывающая инварианты: доказывается при верификации
THEOREM Spec => /\ []TypeInv
                /\ []OSKernelExists
                /\ []SormExists

===============================================================================
