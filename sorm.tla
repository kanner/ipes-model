--------------------------------- MODULE sorm ---------------------------------
EXTENDS types, init, select
-------------------------------------------------------------------------------

\* Предикаты проверки подсистемы управления доступом

SormInitialized ==
    /\ s_sorm \in S_active
    \* прочитан ассоциированный объект o_sorm (правила доступа)
    /\ \E o \in SelectSubjData(s_sorm):
        /\ o.oid = 1
        /\ s_sorm.sid \in o.subj_assoc

SormCheckCreate(s) ==
    /\  \/  /\ \neg SormInitialized
            \* активизируется s_sorm
            /\ s.type = "sorm"
        \* запрос возможен только при активизированном s_sorm
        \/  SormInitialized
    /\  s.is_blocked = FALSE
    \* дополнительные проверки (идентификация/аутентификация и т.д.)

SormCheckPerm(s,oid,r) ==
    \* запрос разрешен s_0 и s_sorm
    /\  \/ s.sid \in {s_0.sid, s_sorm.sid}
        \* либо должен быть активизирован s_sorm
        \/ SormInitialized
    \* запросы к o_sorm может совершать только s_sorm
    /\  \/  /\ oid = o_sorm.oid
            /\ s.sid = s_sorm.sid
            \* удалять или исполнять o_sorm нельзя
            /\ r \notin {"exec","create","delete"}
        \/  oid # o_sorm.oid
            \* дополнительные проверки (правила доступа и т.д.)

===============================================================================
