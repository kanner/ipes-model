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

SormCheckPerm(s) ==
    \* запрос разрешен s_0
    /\  \/  /\ s.sid = s_0.sid
    \* либо должен быть активизирован s_sorm
        \/  /\ SormInitialized

===============================================================================
