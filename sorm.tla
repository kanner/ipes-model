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
    /\  IF  \neg SormInitialized
        THEN \* активизируется s_sorm
             /\ sc.type = "sorm"
        ELSE \* запрос возможен только при активизированном s_sorm
             /\ SormInitialized
    \* delete_subject
    /\  IF  r \in QueriesStateChange
        THEN \* s_0, s_sorm не могут уничтожиться после активизации
             /\ sc \notin {s_0, s_sorm}
    \* create_user, create_shadow
        ELSE IF r \in QueriesAssocChange
        THEN \* субъект не должен быть заблокирован
             /\ sc.is_blocked = FALSE
    \* change_blocked
        ELSE IF r \in QueriesSystem
        THEN \* Административные действия выполняет только s_sorm
             /\ o.subj_assoc = {s_sorm.sid}
             \* Блокировать s_0 или s_sorm нельзя
             /\ sc \notin {s_0, s_sorm}
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
             \* изменение может совершать ассоц. субъект, либо
             \* объект должен быть в O_na (нельзя изменять/удалять
             \* чужие ассоциированные объекты)
             THEN   /\ o.subj_assoc \subseteq {s.sid}
                    \* s_0 и другие не должны изменить o_sorm
                    /\ o # o_sorm
             ELSE
             IF r \in QueriesAssocChange
             THEN   \* контроль целостности: нельзя изменять ассоц.
                    \* объекты с помощью измененных объектов данных;
                    \* субъект может породиться сам (без
                    \* каскадных сессий) или от имени s_0
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
