-------------------------------- MODULE types ---------------------------------
EXTENDS Integers
-------------------------------------------------------------------------------

\* Множества идентификаторов
SubjectIDs  == 0..4
ObjectIDs   == 0..10

\* Модельные значения состояний объектов
ObjectStates== 0..10

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
