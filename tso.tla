---- MODULE tso ----
EXTENDS Naturals, Sequences

CONSTANTS QSize, NULL, Owner, Thieves, EMPTY

VARIABLES deq, mem_bot, wb_bot, next_job, popped, popped_log, pc, age_top, age_tag, cas_fail_log

vars == << deq, mem_bot, wb_bot, next_job, popped, popped_log, pc, age_top, age_tag, cas_fail_log >>

Init == 
    /\ mem_bot = 0
    /\ wb_bot = EMPTY
    /\ next_job = 0
    /\ popped = {}
    /\ popped_log = << >>
    /\ age_top = 0
    /\ age_tag = 0
    /\ cas_fail_log = {}
    /\ pc = [t \in ({Owner} \cup Thieves) |-> "ready"]
    /\ deq = [i \in 0 .. (QSize-1) |-> NULL]

ReadBot ==
    IF wb_bot = EMPTY THEN mem_bot ELSE wb_bot

FlushBot ==
    /\ wb_bot # EMPTY
    /\ mem_bot' = wb_bot
    /\ wb_bot' = EMPTY
    /\ UNCHANGED <<deq, next_job, popped, popped_log, pc, age_tag, age_top, cas_fail_log>>

OwnerPushBottom ==
    /\ pc[Owner] = "ready"
    /\ LET b == ReadBot IN 
         /\ b < QSize
         /\ deq[b] = NULL
         /\ deq' = [deq EXCEPT ![b] = next_job]
         /\ wb_bot' = b + 1
         /\ next_job' = next_job + 1
         /\ pc' = [pc EXCEPT ![Owner] = "ready"]
         /\ UNCHANGED <<mem_bot, popped, popped_log, age_tag, age_top, cas_fail_log>>

ThiefPopTop(t) ==
    /\ t \in Thieves
    /\ pc[t] = "ready"
    /\ (
        \* Attempt to steal
        \/ /\ age_top < mem_bot
           /\ LET oldTop == age_top
                  oldTag == age_tag
                  job == deq[oldTop]
              IN 
                 \* CAS success branch
                 \/ /\ age_top = oldTop /\ age_tag = oldTag
                    /\ age_top' = oldTop + 1
                    /\ popped' = popped \cup {job}
                    /\ popped_log' = Append(popped_log, job)
                    /\ cas_fail_log' = cas_fail_log
                    /\ UNCHANGED age_tag
                
                 \* CAS failure branch
                 \/ /\ age_top # oldTop \/ age_tag # oldTag
                    /\ UNCHANGED <<age_top, age_tag, popped, popped_log, cas_fail_log>>

        \* Nothing to steal
        \/ /\ age_top >= mem_bot
           /\ UNCHANGED <<age_top, age_tag, popped, popped_log, cas_fail_log>>
       )
    /\ pc' = [pc EXCEPT ![t] = "ready"]
    /\ UNCHANGED <<deq, mem_bot, wb_bot, next_job>>

OwnerPopBottom ==
    /\ pc[Owner] = "ready"
    /\ LET b == ReadBot
           idx == b - 1
       IN 
          (
            \* empty
            \/ /\ b = 0
               /\ popped' = popped
               /\ popped_log' = popped_log
               /\ wb_bot' = wb_bot
               /\ UNCHANGED <<deq, mem_bot, age_top, age_tag, cas_fail_log>>
            
            \* more than one element
            \/ /\ b > 0 /\ idx > age_top
               /\ LET job == deq[idx] IN 
                    /\ popped' = popped \cup {job}
                    /\ popped_log' = Append(popped_log, job)
                    /\ wb_bot' = idx
                    /\ UNCHANGED <<deq, mem_bot, age_top, age_tag, cas_fail_log>>
            
            \* single item
            \/ /\ b > 0 /\ idx = age_top
               /\ LET  job == deq[idx]
                       oldTop == age_top
                       oldTag == age_tag
                       newTop == 0
                       newTag == oldTag + 1
                   IN 
                      \* CAS success
                      \/ /\ age_top = oldTop /\ age_tag = oldTag
                         /\ age_top' = newTop
                         /\ age_tag' = newTag
                         /\ popped' = popped \cup { job }
                         /\ popped_log' = Append(popped_log, job)
                         /\ wb_bot' = 0
                         /\ UNCHANGED <<deq, mem_bot, cas_fail_log>>
                      
                      \* CAS fail
                      \/ /\ age_top # oldTop \/ age_tag # oldTag
                         /\ cas_fail_log' = cas_fail_log \cup {"OwnerCASFail"}
                         /\ UNCHANGED <<deq, mem_bot, wb_bot, popped, popped_log, age_top, age_tag>>
          )
    /\ pc' = [pc EXCEPT ![Owner] = "ready"]
    /\ UNCHANGED <<next_job>>

OwnerStep ==
    \/ OwnerPushBottom
    \/ OwnerPopBottom

ThiefStep ==
    \E t \in Thieves: ThiefPopTop(t)

Next == 
    \/ OwnerStep
    \/ ThiefStep
    \/ FlushBot

BotWithinBounds ==
    mem_bot <= QSize

NoDuplicatePop ==
    IF Len(popped_log) <= 1 THEN TRUE
    ELSE \A i, j \in 1..Len(popped_log) :
            i # j => popped_log[i] # popped_log[j]

AgeTopWithinBounds ==
    age_top <= mem_bot

ValidPoppedRange ==
    \A i \in 1..Len(popped_log) :
        popped_log[i] \in 0..(QSize-1)

NoCASFail ==
    cas_fail_log = {}

====