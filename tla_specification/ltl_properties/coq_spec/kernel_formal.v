(* ================================================================ *)
(* Alalawi Deterministic Sovereign Core (ADSC-HCSP)                *)
(* Formal Coq Proof                                                *)
(* ================================================================ *)

Require Import ZArith.
Open Scope Z_scope.

(* ================================================================ *)
(* 1. STATE DEFINITION (Matching C struct and TLA+ State)          *)
(* ================================================================ *)

Record State := {
  R : Z;
  N : Z
}.

(* ================================================================ *)
(* 2. TRANSITION FUNCTION (Matching C transition_function)         *)
(* ================================================================ *)

Definition transition_function (current : State) (i : Z) : State :=
  let numerator := current.(R) * 105 in
  let denominator := 100 + (i * 2) in
  {| R := numerator / denominator; N := i |}.

(* ================================================================ *)
(* 3. VALID INPUT CONDITION (Matching requires / TLA+ ValidInput)  *)
(* ================================================================ *)

Definition ValidInput (current : State) (i : Z) : Prop :=
  0 <= current.(R) <= 20000000 /\
  0 <= i < 1000.

(* ================================================================ *)
(* 4. LIVENESS CHECK FUNCTION (Matching verify_liveness)           *)
(* ================================================================ *)

Definition liveness_check (s : State) : Z :=
  if Z_gt_dec s.(R) 0 then 1 else 0.

(* ================================================================ *)
(* 5. SAFETY THEOREM (P1: Ensures result.R >= 0)                   *)
(*    Matches: C ensures, Coq transition_safety, TLA+ Safety,      *)
(*             LTL P1: ◻ (ValidState(s) → T(s,i).R ≥ 0)           *)
(* ================================================================ *)

Theorem safety_property : forall (current : State) (i : Z),
  ValidInput current i ->
  (transition_function current i).(R) >= 0.
Proof.
  intros current i H.
  unfold transition_function.
  destruct H as [H_R_range H_i_range].
  simpl.
  unfold ValidInput in *.
  
  (* Establish numerator >= 0 *)
  assert (numerator_nonneg : current.(R) * 105 >= 0).
  { apply Z.mul_nonneg_nonneg; [apply H_R_range | apply Z.le_0_105]. }
  
  (* Establish denominator > 0 *)
  assert (denominator_pos : 100 + i * 2 > 0).
  { apply Z.add_pos_pos; [apply Z.lt_0_100 | apply Z.mul_nonneg_nonneg; [apply H_i_range | apply Z.le_0_2]]. }
  
  (* Apply Z.div_nonneg *)
  apply Z.div_nonneg; [assumption | now apply Z.gt_lt_0].
Qed.

(* ================================================================ *)
(* 6. LIVENESS RANGE THEOREM (P2: result is 0 or 1)                *)
(*    Matches: C ensures, TLA+ Liveness, LTL P2:                   *)
(*             ◻ (LivenessCheck(s) ∈ {0, 1})                       *)
(* ================================================================ *)

Theorem liveness_range : forall (s : State),
  liveness_check s = 0 \/ liveness_check s = 1.
Proof.
  intros s.
  unfold liveness_check.
  destruct (Z_gt_dec s.(R) 0).
  - right; reflexivity.
  - left; reflexivity.
Qed.

(* ================================================================ *)
(* 7. DETERMINISM THEOREM (P3: Unique successor)                   *)
(*    Matches: LTL P3: ◻ (i1 = i2 → T(s, i1) = T(s, i2))          *)
(* ================================================================ *)

Theorem determinism_property : forall (current : State) (i1 i2 : Z),
  i1 = i2 ->
  transition_function current i1 = transition_function current i2.
Proof.
  intros current i1 i2 H_eq.
  rewrite H_eq.
  reflexivity.
Qed.

(* ================================================================ *)
(* 8. PROGRESS THEOREM (P4: Existence of next state)               *)
(*    Matches: LTL P4: ◻ (∃ next : next = T(s, i))                 *)
(* ================================================================ *)

Theorem progress_property : forall (current : State) (i : Z),
  exists next : State, next = transition_function current i.
Proof.
  intros current i.
  exists (transition_function current i).
  reflexivity.
Qed.

(* ================================================================ *)
(* 9. AGGREGATED THEOREM (All properties together)                 *)
(*    Matches the complete LTL specification:                      *)
(*    ◻ (ValidState(s) → T(s,i).R ≥ 0)                            *)
(*    ∧ ◻ (LivenessCheck(s) ∈ {0,1})                              *)
(*    ∧ ◻ (i1 = i2 → T(s,i1)=T(s,i2))                            *)
(*    ∧ ◻ (∃ next : next = T(s,i))                                *)
(* ================================================================ *)

Theorem complete_spec :
  (forall current i, ValidInput current i -> (transition_function current i).(R) >= 0) /\
  (forall s, liveness_check s = 0 \/ liveness_check s = 1) /\
  (forall current i1 i2, i1 = i2 -> transition_function current i1 = transition_function current i2) /\
  (forall current i, exists next, next = transition_function current i).
Proof.
  split.
  - exact safety_property.
  - split.
    + exact liveness_range.
    + split.
      * exact determinism_property.
      * exact progress_property.
Qed.

(* ================================================================ *)
(* 10. COROLLARY: Safety under all valid inputs (same as TLA+)     *)
(*     Matches: THEOREM Safety == \A current, i : ...               *)
(* ================================================================ *)

Corollary safety_corollary :
  forall current i,
  ValidInput current i ->
  (transition_function current i).(R) >= 0.
Proof.
  exact safety_property.
Qed.

(* ================================================================ *)
(* 11. COROLLARY: Liveness range (same as TLA+ Liveness)           *)
(*     Matches: THEOREM Liveness == \A s : LivenessCheck(s) ∈ {0,1} *)
(* ================================================================ *)

Corollary liveness_corollary :
  forall s,
  liveness_check s = 0 \/ liveness_check s = 1.
Proof.
  exact liveness_range.
Qed.

(* ================================================================ *)
(* END OF COQ PROOF                                                *)
(* ================================================================ *)
