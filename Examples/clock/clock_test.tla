----------------------------- MODULE clock_test -----------------------------

EXTENDS Integers

CONSTANT startHour, alarmHour

VARIABLE hour

HourPassed == hour' = IF hour # 23 THEN hour + 1 ELSE 0

Alarm == hour = alarmHour

Init == hour = startHour

Next == HourPassed

Spec == Init /\ [][Next]_hour

Safety == hour >= 0 /\ hour <= 23

Liveness == <>Alarm
=============================================================================
\* Modification History
\* Last modified Tue Aug 08 03:22:56 NOVT 2023 by andrey
\* Created Fri Aug 04 00:30:31 NOVT 2023 by andrey