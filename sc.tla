---- MODULE sc ----
EXTENDS Naturals, Sequences

CONSTANTS QSize, NULL, Owner, Thieves

VARIABLES deq, bot, top, popped, pc

vars == << deq, bot, top, popped, pc >>

Init == 
    /\ bot = 0
    /\ top = 0
    /\ popped = {}
    /\ pc = [t \in ({Owner} \cup Thieves) |-> "ready"]
    /\ deq = [i \in 0 .. (QSize-1) |-> NULL]

OwnerPushBottom ==
    /\ pc[Owner] = "ready"
    /\ bot < QSize
    /\ deq' = [deq EXCEPT ![bot] = bot]
    /\ bot' = bot + 1
    /\ pc' = [pc EXCEPT ![Owner] = "ready"]
    /\ UNCHANGED <<top, popped>>

ThiefPopTop(t) ==
    /\ t \in Thieves
    /\ pc[t] = "ready"
    /\ (
        \/ /\ top < bot
           /\ LET job == deq[top]
              IN  /\ top' = top + 1
                  /\ popped' = popped \cup {job}

        \/ /\ top >= bot
           /\ top' = top
           /\ popped' = popped
       )
    /\ pc' = [pc EXCEPT ![t] = "ready"]
    /\ UNCHANGED <<deq, bot>>

OwnerPopBottom ==
    /\ pc[Owner] = "ready"
    /\ (
        \/ /\ bot = 0
           /\ popped' = popped
           /\ top' = top
           /\ bot' = bot
           /\ deq' = deq

        \/ /\ bot > 0
           /\ bot - 1 > top
           /\ LET idx == bot - 1 IN 
                 /\ popped' = popped \cup { deq[idx] }
                 /\ bot' = idx
                 /\ top' = top
                 /\ deq' = deq
        
        \/ /\ bot > 0
           /\ bot - 1 = top
           /\ LET idx == bot - 1 IN 
                 /\ popped' = popped \cup { deq[idx] }
                 /\ bot' = idx
                 /\ top' = top
                 /\ deq' = deq
        )
    /\ pc' = [pc EXCEPT ![Owner] = "ready"]

OwnerStep ==
    \/ OwnerPushBottom
    \/ OwnerPopBottom

ThiefStep ==
    \E t \in Thieves: ThiefPopTop(t)

Next == 
    \/ OwnerStep
    \/ ThiefStep

BotWithinBounds ==
    bot <= QSize

TopLeBot ==
    top <= bot

PoppedNoNull ==
    NULL \notin popped

NoDuplicatePop ==
    \A x \in popped:
        \A y \in popped: x = y \/ x # y


====
