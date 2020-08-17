------------------------------ MODULE types -------------------------------
EXTENDS Integers, FiniteSets
---------------------------------------------------------------------------

\* Множества идентификаторов
SubjectIDs  == 0..3
ObjectIDs   == 0..3 \* TODO: 5+

\* Модельные значения состояний объектов
\* 0 - объект изменялся только единственным ассоциированным субъектом
\* 1 - объект изменялся другим субъектом
ObjectStates == 0..1

\* Типы сущностей системы
SubjTypes == {"users","system","sorm"}
ObjTypes == {"func","data","na"}

\* Типы запросов к системе
QueryTypes == {"change_blocked", "initial", \* только в начальном состоянии
               "create_process", "delete_process",
               "create_user", "create_shadow", "delete_subject",
               "exec",
               "read", "write", "create", "delete"}

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

===========================================================================
