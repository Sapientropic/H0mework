import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MandateEvolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalHistory

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type} (bound : Mandate.Challenge.ProgrammeFamily base scope Index) (inputs : Index)

open Mandate.Challenge

theorem a_single_item_visit_has_its_unique_actual_position (position : Position bound inputs)
    (single : (Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems (bound.inputAt inputs)
      (ProgrammeHistory.visitAt (bound.inputAt inputs) position.ordinal).current).length = 1) :
    positionsAt bound inputs position.ordinal = [position] := by
  have length : (positionsAt bound inputs position.ordinal).length = 1 := by
    simpa only [positionsAt, List.length_map, List.length_finRange] using single
  obtain ⟨other, shape⟩ := List.length_eq_one_iff.mp length
  have inside : position ∈ positionsAt bound inputs position.ordinal := by
    apply List.mem_map.mpr
    exact ⟨position.index, List.mem_finRange _, by cases position; rfl⟩
  rw [shape] at inside
  rw [← List.mem_singleton.mp inside] at shape
  exact shape

private theorem renewed_position (original : Claim bound inputs) (position : Position bound inputs)
    (receipt : Reconfirmation bound inputs original)
    (decoded : readReconfirmation bound inputs original position = some receipt) : receipt.target.position = position := by
  unfold readReconfirmation at decoded
  cases found : read bound inputs position with
  | none => simp only [found] at decoded; contradiction
  | some target =>
    simp only [found] at decoded
    split at decoded
    · cases Option.some.inj decoded
      exact read_position bound inputs position target found
    · contradiction

private def Aligned (original : Claim bound inputs) (attempt : Position bound inputs) : History bound inputs original → Prop
  | .closed .. => True
  | .pending target .. =>
      (target.claim bound inputs).snapshot bound inputs = original.snapshot bound inputs ∧
        (target.claim bound inputs).position.ordinal < attempt.ordinal

variable (original : Claim bound inputs) (attempt : Position bound inputs)
  (later : original.position.ordinal < attempt.ordinal)
  (birth : (MandateEvolution.currentAt base scope bound inputs original.position.ordinal).technology = original.snapshot bound inputs)
  (same : (MandateEvolution.currentAt base scope bound inputs original.position.ordinal).technology =
    (MandateEvolution.currentAt base scope bound inputs attempt.ordinal).technology)

include birth same in
private theorem aligned_receive (history : History bound inputs original) (position : Position bound inputs)
    (earlier : position.ordinal < attempt.ordinal) (aligned : Aligned bound inputs original attempt history) :
    Aligned bound inputs original attempt (history.receive bound inputs position) := by
  cases history with
  | closed state archive slots => trivial
  | pending target state slots =>
    cases renewed : readReconfirmation bound inputs original position with
    | some receipt =>
      have actual := renewed_position bound inputs original position receipt renewed
      have first : original.position.ordinal ≤ position.ordinal := by
        rcases receipt.later with strict | ⟨equal, _⟩
        · rw [actual] at strict; exact Nat.le_of_lt strict
        · rw [actual] at equal; exact Nat.le_of_eq equal
      have snapshot := MandateEvolution.equal_endpoints_preserve_every_intermediate_snapshot
        base scope bound inputs original.position.ordinal attempt.ordinal same position first earlier
      have targetSnapshot : receipt.target.snapshot bound inputs = original.snapshot bound inputs := by
        unfold Claim.snapshot
        rw [actual]
        exact snapshot.trans birth
      simp only [History.receive, renewed]
      split
      · exact ⟨targetSnapshot, by change receipt.target.position.ordinal < attempt.ordinal; rw [actual]; exact earlier⟩
      · exact aligned
    | none =>
      cases attempted : readAttempt bound inputs (target.claim bound inputs) position with
      | none => simpa only [History.receive, renewed, attempted] using aligned
      | some receipt =>
        simp only [History.receive, renewed, attempted]
        split
        · trivial
        · exact aligned

include birth same in
private theorem aligned_fold (history : History bound inputs original) (positions : List (Position bound inputs))
    (earlier : ∀ position ∈ positions, position.ordinal < attempt.ordinal)
    (aligned : Aligned bound inputs original attempt history) :
    Aligned bound inputs original attempt (positions.foldl (History.receive bound inputs) history) := by
  induction positions generalizing history with
  | nil => exact aligned
  | cons position tail ih =>
    exact ih _ (fun next member => earlier next (List.mem_cons_of_mem _ member))
      (aligned_receive bound inputs original attempt birth same history position (earlier _ List.mem_cons_self) aligned)

include later birth same in
private theorem aligned_through (count : Nat) (before : count ≤ attempt.ordinal) :
    Aligned bound inputs original attempt (through bound inputs original count) := by
  induction count with
  | zero => exact ⟨rfl, later⟩
  | succ count ih =>
    apply aligned_fold bound inputs original attempt birth same
    · intro position member
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      change count < attempt.ordinal
      omega
    · exact ih (by omega)

theorem terminal_through_persists (claim : Claim bound inputs) (count last : Nat)
    (terminal : (through bound inputs claim count).isPending bound inputs = false) (ordered : count ≤ last) :
    (through bound inputs claim last).isPending bound inputs = false := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [← continuation_is_own_actual_history bound inputs claim count distance]
  cases actual : through bound inputs claim count with
  | pending target state slots => simp only [actual, History.isPending] at terminal; contradiction
  | closed state archive slots =>
    rw [a_terminal_archive_is_never_replaced]
    rfl

include later birth same in
theorem an_actual_paid_withdrawal_closes_the_complete_native_history
    (singleton : positionsAt bound inputs attempt.ordinal = [attempt])
    (edge : (attempt.item bound inputs).before.technology =
      (MandateEvolution.currentAt base scope bound inputs attempt.ordinal).technology)
    (withdrawal : Withdrawal (scope := scope) (attempt.item bound inputs).before (attempt.item bound inputs).request)
    (accepted : (Mandate.law base scope).Valid (attempt.item bound inputs).before (attempt.item bound inputs).request)
    (count : Nat) (inside : attempt.ordinal < count) :
    (through bound inputs original count).isPending bound inputs = false := by
  have aligned := aligned_through bound inputs original attempt later birth same attempt.ordinal (Nat.le_refl _)
  have unsigned : ¬ Submission (scope := scope) (attempt.item bound inputs).request := by
    obtain ⟨_, request⟩ | ⟨_, request⟩ | ⟨_, _, request⟩ := withdrawal_commands _ _ withdrawal
      <;> rw [request] <;> simp [Submission, Mandate.request]
  have noClaim : read bound inputs attempt = none := by
    simp only [Mandate.Challenge.read, dif_neg unsigned]
  have noRenew : readReconfirmation bound inputs original attempt = none := by
    simp only [readReconfirmation, noClaim]
  have terminal : (through bound inputs original (attempt.ordinal + 1)).isPending bound inputs = false := by
    rw [through, singleton]
    simp only [List.foldl_cons, List.foldl_nil]
    cases actual : through bound inputs original attempt.ordinal with
    | closed state archive slots => rfl
    | pending target state slots =>
      rw [actual] at aligned
      have laterTarget : Later bound inputs (target.claim bound inputs).position attempt := Or.inl aligned.2
      have sameTarget : (attempt.item bound inputs).before.technology = (target.claim bound inputs).snapshot bound inputs := by
        exact (edge.trans (same.symm.trans birth)).trans aligned.1.symm
      have checked : Later bound inputs (target.claim bound inputs).position attempt ∧
          Withdrawal (scope := scope) (attempt.item bound inputs).before (attempt.item bound inputs).request ∧
          (attempt.item bound inputs).before.technology = (target.claim bound inputs).snapshot bound inputs :=
        ⟨laterTarget, withdrawal, sameTarget⟩
      simp only [History.receive, noRenew, readAttempt, dif_pos checked, dif_pos accepted, History.isPending]
  exact terminal_through_persists bound inputs original (attempt.ordinal + 1) count terminal inside

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalHistory
