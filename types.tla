-------------------------------- MODULE types ---------------------------------
EXTENDS Integers, FiniteSets
-------------------------------------------------------------------------------

\* Множества идентификаторов
SubjectIDs  == 0..3
ObjectIDs   == 0..3 \* TODO: 5+

\* Модельные значения состояний объектов
ObjectStates == 0..1 \* TODO: 5
ObjectStateMax == Cardinality(ObjectStates) - 1

\* Типы сущностей системы
SubjTypes == {"users","system","sorm"}
ObjTypes == {"func","data","na"}

-------------------------------------------------------------------------------

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
             \* [o] - состояние объекта, 0 - пустой объект
             state: ObjectStates]

===============================================================================
