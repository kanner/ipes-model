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

SormCheckCreate(s) ==
    /\  \/  /\ \neg SormInitialized
            \* активизируется s_sorm
            /\ s.type = "sorm"
        \* запрос возможен только при активизированном s_sorm
        \/  SormInitialized
    /\  s.is_blocked = FALSE
    \* дополнительные проверки (идентификация/аутентификация и т.д.)

SormCheckPerm(s,id,r) ==
    \* запрос разрешен s_0 и s_sorm
    /\  IF s.sid \in {s_0.sid, s_sorm.sid}
        THEN TRUE
        \* либо должен быть активизирован s_sorm
        ELSE SormInitialized
    \* удалять или исполнять o_sorm нельзя
    /\  IF id = o_sorm.oid
        \* иначе нарушится SormInitialized
        THEN r \notin {"exec","create","delete"}
        ELSE TRUE
    \* правила для выполнения свойств корректности модели ИПСС
    /\  IF \E o \in SelectObjects: o.oid = id
        THEN IF r \in QueriesStateChange
             \* изменение может совершать ассоц. субъект, или объект в O_na
             THEN   /\ SelectObject(id).subj_assoc \subseteq {s.sid}
                    \* s_0 и другие не должны изменить o_sorm
                    /\ SelectObject(id) # o_sorm
             ELSE
             IF r \in QueriesAssocChange
             THEN   \* нельзя изменять ассоциированные объекты с помощью
                    \* измененных объектов данных: контроль целостности
                    /\ SelectObject(id).state # StateChanged
             ELSE   /\ TRUE
        ELSE \* создание новых объектов
            TRUE
    \* другие дополнительные проверки (правила доступа и т.д.)
    \* при нарушении - запрос запрещен

===========================================================================
