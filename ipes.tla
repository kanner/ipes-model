--------------------------------- MODULE ipes ---------------------------------
EXTENDS init, types, select, sorm
-------------------------------------------------------------------------------

\* CreateProcessD
\* Создание функционально ассоциированного объекта
CreateProcess(s,o,x) ==
        /\ O_func' = O_func \cup {[oid |-> x,
                                   type |-> "func",
                                   subj_assoc |-> {s.sid},
                                   \* форк наследует состояние
                                   state |-> o.state]}
        /\ Q' = Append(Q, [subj |-> s, proc |-> o,
                           dent |-> (CHOOSE f \in O_func': f.oid = x),
                           type |-> "create_process"])
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
        /\ Q' = Append(Q, [subj |-> s, proc |-> o,
                           dent |-> o,
                           type |-> "delete_process"])
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
        /\ Q' = Append(Q, [subj |-> s,
                           proc |-> (CHOOSE f \in O_func': f.oid = o.oid),
                           dent |-> s_u,
                           type |-> "create_user"])
        /\ UNCHANGED <<O_data, O_na, S>>

CreateUserD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E s_u \in (S \ S_active): \* TODO: множество сессий?

            \* TODO: \/ s.sid = s_0.sid
            \*       \/ s.type = "users"

            \* Новый субъект типа "users"
            /\ s_u.type = "users"

            \* Правила порождения s_sorm
            /\ SormCheckCreate(s_u)

            \* Нельзя порождать из последнего процесса
            /\ Cardinality(SelectSubjProc(s)) > 1

            \* Постусловия
            /\ CreateUser(s,o,s_u)

\* CreateShadowD
\* Порождения системного субъекта из объекта
CreateShadow(s,o,s_w) ==
        /\ S_active' = S_active \cup {s_w}
        /\ O_func' = (O_func \ {o}) \cup {[ o EXCEPT!["subj_assoc"]= {s_w.sid}]}
        /\ Q' = Append(Q, [subj |-> s,
                           proc |-> (CHOOSE f \in O_func': f.oid = o.oid),
                           dent |-> s_w,
                           type |-> "create_shadow"])
        /\ UNCHANGED <<O_data, O_na, S>>

CreateShadowD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E s_w \in (S \ S_active):

            \* Порождение может выполнять только субъект s_0
            /\ s.sid = s_0.sid

            \* Новый субъект типа "system" или "sorm"
            /\ s_w.type \in {"system", "sorm"}

            \* Правила порождения s_sorm
            /\ SormCheckCreate(s_w)

            \* Нельзя порождать из последнего процесса
            /\ Cardinality(SelectSubjProc(s)) > 1

            \* Постусловия
            /\ CreateShadow(s,o,s_w)

\* DeleteSubjectD
\* Уничтожение всех функционально ассоциированных объектов
DeleteSubject(s,o) ==
        \* Для всех процессов выполняется DeleteProcess()
        /\ \A proc \in SelectSubjProc(s):
            /\ O_func' = O_func \ {proc}
            \* Объекты-данные перестают быть ассоциированными
        /\  \/  /\ Cardinality(SelectSubjData(s)) > 0
                /\ \A d \in SelectSubjData(s):
                        \* Неассоциированный объект должен перейти в O_na
                    /\  \/  /\ Cardinality(d.subj_assoc) = 1
                            /\ O_data' = O_data \ {d}
                            /\ O_na' = O_na \cup
                                {[oid |-> d.oid,
                                  type |-> "na",
                                  subj_assoc |-> {},
                                  state |-> d.state]}
                        \* Из ассоциированных объектов исключается s.sid
                        \/  /\ Cardinality(d.subj_assoc) > 1
                            /\ O_data' = (O_data \ {d}) \cup
                                {[ d EXCEPT!["subj_assoc"]=
                                    (d.subj_assoc \ {s.sid})]}
                            /\ O_na' = O_na
            \/  /\ Cardinality(SelectSubjData(s)) = 0
                /\ O_data' = O_data
                /\ O_na' = O_na
        /\ S_active' = S_active \ {s}
        /\ Q' = Append(Q, [subj |-> s, proc |-> o,
                           dent |-> s,
                           type |-> "delete_subject"])
        /\ UNCHANGED <<S>>

DeleteSubjectD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):

            \* s_0, s_sorm не могут уничтожиться после активизации
            /\ s.sid # s_0.sid
            /\ s.sid # s_sorm.sid

            \* Постусловия
            /\ DeleteSubject(s,o)

\* ExecD
\* Загрузка бинарного образа для выполнения
Exec(s,o,o_e) ==
        \* Бинарный файл загружается в процесс
        /\ O_func' = (O_func \ {o}) \cup
                {[ o EXCEPT!["state"]=
                    o_e.state]}
            \* Объект перестает быть ассоциированным и переходит в O_na
        /\  \/  /\ Cardinality(o_e.subj_assoc) = 1
                /\ O_data' = O_data \ {o_e}
                /\ O_na' = O_na \cup
                    {[oid |-> o_e.oid,
                      type |-> "na",
                      subj_assoc |-> {},
                      state |-> o_e.state]}
            \* Из ассоциированного объекта исключается s.sid
            \/  /\ Cardinality(o_e.subj_assoc) > 1
                /\ O_data' = (O_data \ {o_e}) \cup
                    {[ o_e EXCEPT!["subj_assoc"]=
                        (o_e.subj_assoc \ {s.sid})]}
                /\ O_na' = O_na
        /\ Q' = Append(Q, [subj |-> s,
                           proc |-> (CHOOSE f \in O_func': f.oid = o.oid),
                           dent |-> (CHOOSE d \in O_data' \cup O_na':
                                            d.oid = o_e.oid),
                           type |-> "exec"])
        /\ UNCHANGED <<S_active, S>>

ExecD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \* Объект уже прочитан
        \E o_e \in SelectSubjData(s):

            \* Правила доступа s_sorm
            /\ SormCheckPerm(s,o_e.oid,"exec")

            \* Постусловия
            /\ Exec(s,o,o_e)

\* ReadD
\* Реализация информационного потока на чтение
Read(s,o,o_r) ==
        \* Процесс читает данные и изменяет свое состояние
        /\ O_func' = (O_func \ {o}) \cup
                {[ o EXCEPT!["state"]=
                    o_r.state]}
        \* Объект с данными становится ассоциированным
        /\ O_data' = (O_data \ {o_r}) \cup
            {[oid |-> o_r.oid,
              type |-> "data",
              subj_assoc |-> (o_r.subj_assoc \cup {s.sid}),
              state |-> o_r.state]}
        /\ O_na' = O_na \ {o_r}
        /\ Q' = Append(Q, [subj |-> s,
                           proc |-> (CHOOSE f \in O_func': f.oid = o.oid),
                           dent |-> (CHOOSE d \in O_data': d.oid = o_r.oid),
                           type |-> "read"])
        /\ UNCHANGED <<S_active, S>>

ReadD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E o_r \in SelectObjects \ O_func:

            \* Правила доступа s_sorm
            /\ SormCheckPerm(s,o_r.oid,"read")

            \* Постусловия
            /\ Read(s,o,o_r)

\* WriteD
\* Реализация информационного потока на запись
Write(s,o,o_w) ==
        \* Изменяется состояние объекта
        /\  \/  /\ o_w \in O_na
                /\ O_na' = (O_na \ {o_w}) \cup
                        {[ o_w EXCEPT!["state"]= 0]}
                /\ O_data' = O_data
            \/  /\ o_w \in O_data
                \* если еще с кем-то ассоциирован - изменим состояние
                /\  \/  /\ o_w.subj_assoc # {s.sid}
                        /\ O_data' = (O_data \ {o_w}) \cup
                                {[ o_w EXCEPT!["state"]= 1]}
                        \* запись в свои объекты не меняет состояния
                    \/  /\ o_w.subj_assoc = {s.sid}
                        /\ O_data' = (O_data \ {o_w}) \cup
                                {[ o_w EXCEPT!["state"]= 0]}
                /\ O_na' = O_na
        /\ Q' = Append(Q, [subj |-> s, proc |-> o,
                           dent |-> (CHOOSE d \in O_data' \cup O_na':
                                            d.oid = o_w.oid),
                           type |-> "write"])
        /\ UNCHANGED <<S_active, O_func, S>>

WriteD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E o_w \in SelectObjects \ O_func:

            \* Правила доступа s_sorm
            /\ SormCheckPerm(s,o_w.oid,"write")

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
        /\ Q' = Append(Q, [subj |-> s, proc |-> o,
                           dent |-> (CHOOSE d \in O_na': d.oid = x),
                           type |-> "create"])
        /\ UNCHANGED <<S_active, O_func, O_data, S>>

CreateD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):

        \E x \in ObjectIDs:

            \* Выбор свободного идентификатора
            /\ \A obj \in SelectObjects: obj.oid # x

            \* Правила доступа s_sorm
            /\ SormCheckPerm(s,x,"create")

            \* Постусловия
            /\ Create(s,o,x)

\* DeleteD
\* Реализация информационного потока на удаление объекта
Delete(s,o,o_d) ==
        /\ O_na' = O_na \ {o_d}
        /\ O_data' = O_data \ {o_d}
        \* если еще с кем-то ассоциирован - изменим состояние
        /\  \/  /\ o_d.subj_assoc # {s.sid}
                /\ Q' = Append(Q, [subj |-> s, proc |-> o,
                                   dent |-> [ o_d EXCEPT!["state"]= 1],
                                   type |-> "delete"])
            \* удаление своих объектов не меняет состояния
            \/  /\ o_d.subj_assoc = {s.sid}
                /\ Q' = Append(Q, [subj |-> s, proc |-> o,
                                   dent |-> o_d,
                                   type |-> "delete"])
        /\ UNCHANGED <<S_active, O_func, S>>

DeleteD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \E o_d \in SelectObjects \ O_func:

            \* Правила доступа s_sorm
            /\ SormCheckPerm(s,o_d.oid,"delete")

            \* Постусловия
            /\ Delete(s,o,o_d)

-------------------------------------------------------------------------------

\* SormBlockSubjectD
\* Изменение блокировки субъекта (разрешенный / неразрешенный)
SormBlockSubject(s,o,s_b) ==
        /\ S' = (S \ {s_b}) \cup
            {[ s_b EXCEPT!["is_blocked"]= (\neg s_b.is_blocked) ]}
        /\ Q' = Append(Q, [subj |-> s, proc |-> o,
                           dent |-> (CHOOSE su \in S': su.sid = s_b.sid),
                           type |-> "change_blocked"])
        /\ UNCHANGED <<S_active, O_func, O_data, O_na>>

SormBlockSubjectD ==
        \E s \in S_active:
        \E o \in SelectSubjProc(s):
        \* для уменьшения возможных состояний блокировать можно
        \* только неактивного пользователя
        \E s_b \in S \ S_active:

            \* Административные действия выполняет только s_sorm
            /\ s.sid = s_sorm.sid

            \* Блокировать s_0 или s_sorm нельзя
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
            /\ SelectPrevQuery(Q) \in Queries

\* Consistency Invariant
\* Инвариант консистентности множеств сущностей системы
ConsistencyInv ==
    /\ \A proc \in O_func:
        \* объект м.б. функционально ассоциирован только с одним субъектом
        /\ Cardinality(proc.subj_assoc) = 1
        /\ \E subj \in S_active: proc.subj_assoc = {subj.sid}
        \* объект не может состоять в другом множестве
        /\ proc \notin O_data \cup O_na
    /\ \A data \in O_data:
        \* объект м.б. ассоциирован как данные с несколькими субъектами
        /\ Cardinality(data.subj_assoc) >= 1
        /\ \E subj \in S_active: subj.sid \in data.subj_assoc
        /\ data \notin O_func \cup O_na
    /\ \A obj \in O_na:
        \* объект м.б. не ассоциирован ни с одним субъектом
        /\ Cardinality(obj.subj_assoc) = 0
        /\ obj \notin O_func \cup O_data
    \* уникальность идентификаторов субъектов и объектов
    /\ \A sid \in SubjectIDs:
        /\ Cardinality({s \in S: s.sid = sid}) <= 1
    /\ \A oid \in ObjectIDs:
        /\ Cardinality({o \in SelectObjects: o.oid = oid}) <= 1

\* Blocked Invariant
\* Неразрешенные субъекты не могут быть активными и
\* иметь ассоциированные объекты
BlockedInv ==
    \A s \in S:
        /\  \/  /\ s.is_blocked = TRUE
                /\ s \notin S_active
                /\ ~\E o \in SelectObjects: s.sid \in o.subj_assoc
            \/ s.is_blocked = FALSE

\* OSKernelExists
\* В любой момент времени существует s_0
OSKernelExists ==
    /\ s_0 \in S_active
    /\ s_0.is_blocked = FALSE

\* SormInits
\* В начальный момент времени инициализирован s_sorm
\* либо функционирует только s_0
SormInits ==
    /\  \/  /\ s_sorm \in S_active
            /\ s_sorm.is_blocked = FALSE
        \/  /\ s_sorm \notin S_active
            /\ S_active = {s_0}

\* Correctness
\* Свойство корректности субъектов при переходе системы
Correctness ==
    \* Нельзя изменять состояние ассоциированных объектов другого субъекта
    /\  \/  /\ SelectPrevQueryDent(Q) \in Objects
            /\  \/  /\ SelectPrevQueryDent(Q).type \in {"func", "data"}
                    /\ SelectPrevQueryDent(Q).state # 1
                \/  /\ SelectPrevQueryDent(Q).type = "na"
        \* изменен функционально ассоциированный объект
        \/  /\ SelectPrevQueryDent(Q) \in Subjects
            /\ SelectPrevQueryProc(Q).state # 1

\* AbsCorrectnessOpp
\* Свойство абсолютной корректности субъектов в обратном смысле
AbsCorrectnessOpp ==
    /\  \/  /\ SelectPrevQueryDent(Q) \in Objects
            \* объектами-данными не может стать измененный ранее объект
            /\  \/  /\ SelectPrevQueryType(Q) = "read"
                    /\ ~\E q \in SelectQueries(Q, Len(Q)-1, {"write","delete"}):
                        /\ q.dent = SelectPrevQueryDent(Q)
                        \* изменять мог только субъект, осуществляющий чтение
                        /\ q.subj # SelectPrevQuerySubj(Q)
                \/  TRUE
            \* функционально ассоц. объектом не может стать измененный ранее объект
        \/  /\ SelectPrevQueryDent(Q) \in Subjects
            /\  \/  /\ SelectPrevQueryType(Q) \in {"create_user","create_shadow"}
                    /\ ~\E q \in SelectQueries(Q, Len(Q)-1, {"read","exec"}):
                        /\ q.proc = SelectPrevQueryProc(Q)
                        /\ q.subj # SelectPrevQuerySubj(Q)
                \/  TRUE

-------------------------------------------------------------------------------

\* Init
\* Инициализация модели
Init == /\ S_active = {s_0}
        \* изначально существует только s_0 и его процесс o_0
        /\ O_func = {o_0}
        /\ O_data = {}
        /\ O_na = {o_sorm}
        \* остальные субъекты еще не активизированы
        /\ S = {s_0, s_sorm, s_2, s_3}
        /\ Q = <<q_0>>

\* Next
\* Возможные дальнейшие действия модели (запросы к системе)
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
        \/ SormBlockSubjectD

\* Spec
\* Спецификация модели
Spec == Init /\ [][Next]_vars

\* Invariants
\* Теорема, учитывающая инварианты: доказывается при верификации
THEOREM Spec => /\ []TypeInv
                /\ []ConsistencyInv
                /\ []BlockedInv
                /\ []OSKernelExists
                /\ []SormInits
                /\ []Correctness
                /\ []AbsCorrectnessOpp

===============================================================================
