---------------------------- MODULE CounterInc ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

NumThreads == 2
Threads == 1..NumThreads

LoopSize == 1

(*--algorithm counter_inc
variables
    counter = 0;

define
    AllDone ==
        \A t \in Threads: pc[t] = "Done"
    CorrectCounter ==
        AllDone => counter = 2
end define;


process p \in Threads
variables
    index = 0;
    local = 0;
begin
    Loop:
        while index < LoopSize do
            GetIncrement:
                local := counter;
                counter := local+1;
            index := index+1
        end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "50b7c291" /\ chksum(tla) = "31a8c8e6")
VARIABLES counter, pc

(* define statement *)
AllDone ==
    \A t \in Threads: pc[t] = "Done"
CorrectCounter ==
    AllDone => counter = 2

VARIABLES index, local

vars == << counter, pc, index, local >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 0
        (* Process p *)
        /\ index = [self \in Threads |-> 0]
        /\ local = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF index[self] < LoopSize
                    THEN /\ pc' = [pc EXCEPT ![self] = "GetIncrement"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << counter, index, local >>

GetIncrement(self) == /\ pc[self] = "GetIncrement"
                      /\ local' = [local EXCEPT ![self] = counter]
                      /\ counter' = local'[self]+1
                      /\ index' = [index EXCEPT ![self] = index[self]+1]
                      /\ pc' = [pc EXCEPT ![self] = "Loop"]

p(self) == Loop(self) \/ GetIncrement(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
