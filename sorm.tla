------------------------------- MODULE sorm -------------------------------
EXTENDS types, init, select
---------------------------------------------------------------------------

\* Предикаты проверки подсистемы управления доступом

SormInitialized ==
    /\ s_sorm \in S_active
    \* прочитан ассоциированный объект o_sorm (правила доступа)
    /\ \E o \in SelectSubjData(s_sorm):
        /\ o.oid = 1
        /\ s_sorm.sid \in o.subj_assoc

SormCheckSubj(o, sc, r) ==
    /\  \/  /\ \neg SormInitialized
            \* активизируется s_sorm
            /\ sc.type = "sorm"
        \* запрос возможен только при активизированном s_sorm
        \/  SormInitialized
    \* правила для выполнения свойств корректности модели ИПСС
    \* delete_subject
    /\  IF   r \in QueriesStateChange
        THEN
             \* нельзя удалять чужие ассоциированные объекты
             /\ o.subj_assoc = {sc.sid}
             \* s_0, s_sorm не могут уничтожиться после активизации
             /\ sc \notin {s_0, s_sorm}
        ELSE TRUE
    \* create_user, create_shadow
    /\  IF      r \in QueriesAssocChange
        THEN
            \* субъект может породиться сам (без
            \* каскадных сессий) или от имени s_0
            /\ o.state \in {sc.sid, s_0.sid}
            \* субъект не должен быть заблокирован
            /\ sc.is_blocked = FALSE
        ELSE TRUE
    \* дополнительные проверки (идентификация/аутентификация и т.д.)

SormCheckPerm(s,o,r) ==
    \* запрос разрешен s_0 и s_sorm
    /\  IF s.sid \in {s_0.sid, s_sorm.sid}
        THEN TRUE
        \* либо должен быть активизирован s_sorm
        ELSE SormInitialized
    \* удалять или исполнять o_sorm нельзя
    /\  IF o = o_sorm
        \* иначе нарушится SormInitialized
        THEN r \notin {"exec","create","delete"}
        ELSE TRUE
    \* правила для выполнения свойств корректности модели ИПСС
    /\  IF \E obj \in SelectObjects: obj = o
        THEN IF r \in QueriesStateChange
             \* изменение может совершать ассоц. субъект,
             \* либо объект должен быть в O_na
             THEN   /\ o.subj_assoc \subseteq {s.sid}
                    \* s_0 и другие не должны изменить o_sorm
                    /\ o # o_sorm
             ELSE
             IF r \in QueriesAssocChange
             THEN   \* контроль целостности: нельзя изменять ассоц.
                    \* объекты с помощью измененных объектов данных
                    o.state \in {s.sid, s_0.sid} \* # StateChanged
                    \* системные объекты - исключение
             ELSE   TRUE
        ELSE
            \* создание возможно только для личных объектов
            /\ o.subj_assoc \subseteq {s.sid}
            /\ o.state = s.sid
    \* другие дополнительные проверки (правила доступа и т.д.)
    \* при нарушении - запрос запрещен

===========================================================================
