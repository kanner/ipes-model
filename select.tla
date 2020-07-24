------------------------------- MODULE select ---------------------------------
EXTENDS init
-------------------------------------------------------------------------------

\* множество O_t модели ИПСС
SelectObjects == { o \in O_func \cup O_data \cup O_na: TRUE }

\* функционально ассоциированные объекты субъекта
SelectSubjProc(s) == { o \in O_func: s.sid \in o.subj_assoc }

\* ассоциированные объекты-данные субъекта
SelectSubjData(s) == { o \in O_data: s.sid \in o.subj_assoc }

\* выбор сущности, способной активизироваться
SelectSubjAvail == { s \in S \ S_active: s.is_blocked = FALSE }

===============================================================================