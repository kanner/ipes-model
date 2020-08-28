------------------------------ MODULE types -------------------------------
EXTENDS Integers, FiniteSets
---------------------------------------------------------------------------

\* Множества идентификаторов
SubjectIDs  == 0..4
ObjectIDs   == 0..12

\* Модельные значения состояний объектов
\* 0 - объект создан или изменялся субъектом с sid = 0 (системой)
\* 1 - объект cоздан или изменялся субъектом с sid = 1
\* ...
\* 4 - объект изменялся другим субъектом (целостность нарушена)
ObjectStates == 0..Cardinality(SubjectIDs)
StateChanged == Cardinality(ObjectStates) - 1

\* Типы сущностей системы
SubjTypes == {"users","system","sorm"}
ObjTypes == {"func","data","na"}

\* Типы запросов к системе
QueryTypes == {"change_blocked", "initial", \* только в начальном состоянии
               "create_process", "delete_process",
               "create_user", "create_shadow", "delete_subject",
               "exec",
               "read", "write", "create", "delete"}

QueriesSystem == {"change_blocked", "initial"}
QueriesStateChange == {"write", "create", "delete",
                       "create_process", "delete_process"}
    \* TODO: "delete_subject"
QueriesAssocChange == {"create_user", "create_shadow",
                       "exec", "read"}

---------------------------------------------------------------------------

\* Субъекты доступа
Subjects == [sid: SubjectIDs,
             type: SubjTypes,
             \* заблокирован, не зарегистрирован
             is_blocked: BOOLEAN]

\* Объекты доступа
Objects  == [oid: ObjectIDs,
             type: ObjTypes,
             \* субъект, с которым ассоциирован
             subj_assoc: SUBSET SubjectIDs,
             \* [o] - состояние объекта
             state: ObjectStates]

\* Запросы к системе
Queries  == [subj: Subjects,
             proc: Objects,
             dent: Objects \cup Subjects,
             type: QueryTypes]

\* Сущности системы: субъекты и объекты
Entities == Subjects \cup Objects

===========================================================================
