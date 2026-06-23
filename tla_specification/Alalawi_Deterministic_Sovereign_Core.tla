---- MODULE Alalawi_Deterministic_Sovereign_Core ----
EXTENDS Integers

(* ================================================================ *)
(* 1. CONSTANTS (Matching requires / Coq hypotheses)               *)
(* ================================================================ *)

CONSTANTS MaxR, MaxI
ASSUME MaxR = 20000000
ASSUME MaxI = 1000

(* ================================================================ *)
(* 2. STATE DEFINITION (Matching struct State / Record State)      *)
(* ================================================================ *)

State == [R: Int, N: Int]

(* ================================================================ *)
(* 3. TRANSITION FUNCTION (Matching transition_function)           *)
(* ================================================================ *)

Transition(current, i) ==
    LET
        numerator   == current.R * 105
        denominator == 100 + (i * 2)
    IN
        [R |-> numerator \div denominator, N |-> i]

(* ================================================================ *)
(* 4. VALID INPUT CONDITION (Matching requires / Coq hypotheses)   *)
(* ================================================================ *)

ValidInput(current, i) ==
    /\ current.R >= 0 /\ current.R <= MaxR
    /\ i >= 0 /\ i < MaxI

(* ================================================================ *)
(* 5. SAFETY PROPERTY (Matching ensures / Coq theorem)             *)
(* ================================================================ *)

SafetyProperty(current, i) ==
    ValidInput(current, i) => Transition(current, i).R >= 0

(* ================================================================ *)
(* 6. SAFETY THEOREM (Matching Coq theorem transition_safety)      *)
(* ================================================================ *)

THEOREM Safety ==
    \A current, i : ValidInput(current, i) => Transition(current, i).R >= 0

(* ================================================================ *)
(* 7. LIVENESS CHECK (Matching verify_liveness)                    *)
(* ================================================================ *)

LivenessCheck(s) == IF s.R > 0 THEN 1 ELSE 0

(* 8. LIVENESS OUTPUT RANGE (Matching ensures \result == 0 || 1)   *)

LivenessRange(s) == LivenessCheck(s) \in {0, 1}

(* 9. LIVENESS THEOREM (Matching Frama-C ensures)                  *)

THEOREM Liveness == \A s : LivenessRange(s)

====================================
