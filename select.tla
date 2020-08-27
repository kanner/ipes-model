----------------------------- MODULE select -------------------------------
EXTENDS init, Sequences
---------------------------------------------------------------------------

\* множество O_t модели ИПСС
SelectObjects == { o \in O_func \cup O_data \cup O_na: TRUE }

\* функционально ассоциированные объекты: процессы
SelectProc == { o \in O_func: TRUE }

\* функционально ассоциированные объекты субъекта
SelectSubjProc(s) == { o \in O_func: s.sid \in o.subj_assoc }

\* ассоциированные объекты-данные субъекта
SelectSubjData(s) == { o \in O_data: s.sid \in o.subj_assoc }

\* выбор последнего совершенного запроса и его параметров
SelectPrevQuery(Sq) == Sq[Len(Sq)]
SelectPrevQuerySubj(Sq) == SelectPrevQuery(Sq).subj
SelectPrevQueryProc(Sq) == SelectPrevQuery(Sq).proc
SelectPrevQueryDent(Sq) == SelectPrevQuery(Sq).dent
SelectPrevQueryType(Sq) == SelectPrevQuery(Sq).type

\* выбор множества запросов определенного типа
SelectQueries(Sq, L, Types) ==
    {
        q \in Queries:
        \E idx \in 1..L:
            /\ q = Q[idx]
            /\ q.type \in Types
    }

===========================================================================
