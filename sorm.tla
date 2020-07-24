--------------------------------- MODULE sorm ---------------------------------
EXTENDS types, init
-------------------------------------------------------------------------------

\* Предикаты проверки подсистемы управления доступом

SormNotInitialized ==
    /\ \A pid \in ObjectIDs:
        \* не было запросов на создание s_sorm
        Q \cap ({s_0.sid} \X {pid} \X {s_sorm.sid} \X {"create_shadow"}) = {}

SormInitialized ==
    /\ \A pid \in ObjectIDs:
        \* запрос на создание s_sorm выполнялся
        Q \cap ({s_0.sid} \X {pid} \X {s_sorm.sid} \X {"create_shadow"}) # {}
    /\ \A id \in ObjectIDs:
        \* был прочитан ассоциированный объект o_sorm (правила доступа)
        Q \cap ({s_sorm.sid} \X {id} \X {o_sorm.oid} \X {"read"}) # {}

SormCheckCreate(s) ==
    /\  \/  /\ s.type = "sorm"
            \* s_sorm активизируется один раз
            /\ SormNotInitialized
        \/  /\ s.type \in {"system","users"}
            \* запрос возможен только при активизированном s_sorm
            /\ SormInitialized

SormCheckPerm(s) ==
    \* запрос разрешен s_0
    /\  \/  /\ s.sid = s_0.sid
    \* либо должен быть активизирован s_sorm
        \/  /\ SormInitialized

===============================================================================
