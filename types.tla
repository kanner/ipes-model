-------------------------------- MODULE types ---------------------------------
EXTENDS Integers, FiniteSets
-------------------------------------------------------------------------------

\* Множества идентификаторов
SubjectIDs  == 0..4
ObjectIDs   == 0..2 \* TODO: 5+

\* Модельные значения состояний объектов
ObjectStates == 0..5
ObjectStateMax == Cardinality(ObjectStates) - 1

\* Типы сущностей системы
SubjTypes == {"users","system","sorm"}
ObjTypes == {"func","data","na"}

-------------------------------------------------------------------------------

\* Субъекты доступа
Subjects == [sid: SubjectIDs,
             type: SubjTypes,
             is_blocked: BOOLEAN]

\* Объекты доступа
Objects  == [oid: ObjectIDs,
             type: ObjTypes,
             subj_assoc: SUBSET SubjectIDs,
             state: ObjectStates]

===============================================================================
