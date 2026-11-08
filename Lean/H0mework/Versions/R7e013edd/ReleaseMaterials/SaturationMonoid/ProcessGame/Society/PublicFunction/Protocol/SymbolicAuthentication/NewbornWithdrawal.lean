import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletedInventory

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NewbornWithdrawal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type} (bound : ProgrammeFamily base scope Index) (inputs : Index)

theorem a_decoded_reconfirmation_is_an_actual_claim (original : Claim bound inputs)
    (position : Position bound inputs) (receipt : Reconfirmation bound inputs original)
    (found : readReconfirmation bound inputs original position = some receipt) :
    Mandate.Challenge.read bound inputs position = some receipt.target := by
  unfold readReconfirmation at found
  cases decoded : Mandate.Challenge.read bound inputs position with
  | none => simp only [decoded] at found; contradiction
  | some claim =>
    simp only [decoded] at found
    split at found
    · cases Option.some.inj found; rfl
    · contradiction

theorem a_decoded_attempt_is_at_its_actual_position (claim : Claim bound inputs)
    (position : Position bound inputs) (attempt : Attempt bound inputs claim)
    (found : readAttempt bound inputs claim position = some attempt) : attempt.position = position := by
  unfold readAttempt at found
  split at found
  · cases Option.some.inj found; rfl
  · cases found

theorem an_actual_withdrawal_is_not_a_new_claim (position : Position bound inputs)
    (withdrawal : Withdrawal (scope := scope) (position.item bound inputs).before (position.item bound inputs).request) :
    Mandate.Challenge.read bound inputs position = none := by
  have unsigned : ¬ Submission (scope := scope) (position.item bound inputs).request := by
    obtain ⟨_, signed⟩ | ⟨_, signed⟩ | ⟨_, _, signed⟩ := withdrawal_commands _ _ withdrawal
      <;> rw [signed] <;> simp [Submission, Mandate.request]
  simp only [Mandate.Challenge.read, dif_neg unsigned]

theorem no_reconfirmation_before_its_own_birth (claim : Claim bound inputs) (position : Position bound inputs)
    (notLater : ¬ Later bound inputs claim.position position) : readReconfirmation bound inputs claim position = none := by
  cases decoded : Mandate.Challenge.read bound inputs position with
  | none => simp only [readReconfirmation, decoded]
  | some target =>
    have actual := read_position bound inputs position target decoded
    have denied : ¬ (Later bound inputs claim.position target.position ∧ target.signer bound inputs = claim.signer bound inputs) := by
      intro checked
      exact notLater (actual ▸ checked.1)
    simp only [readReconfirmation, decoded, dif_neg denied]

theorem initial_history_ignores_every_not_later_position (claim : Claim bound inputs) (position : Position bound inputs)
    (notLater : ¬ Later bound inputs claim.position position) :
    (History.initial bound inputs claim).receive bound inputs position = History.initial bound inputs claim := by
  have noRenew := no_reconfirmation_before_its_own_birth bound inputs claim position notLater
  have denied : ¬ (Later bound inputs claim.position position ∧
      Withdrawal (scope := scope) (position.item bound inputs).before (position.item bound inputs).request ∧
      (position.item bound inputs).before.technology = claim.snapshot bound inputs) := fun checked => notLater checked.1
  have noAttempt : readAttempt bound inputs claim position = none := by
    unfold readAttempt
    split
    · exact False.elim (denied (by assumption))
    · rfl
  simp only [History.initial, History.receive, noRenew, Target.claim, noAttempt]

private theorem initial_fold (claim : Claim bound inputs) (positions : List (Position bound inputs))
    (notLater : ∀ position ∈ positions, ¬ Later bound inputs claim.position position) :
    positions.foldl (History.receive bound inputs) (History.initial bound inputs claim) = History.initial bound inputs claim := by
  induction positions with
  | nil => rfl
  | cons position tail ih =>
    rw [List.foldl_cons, initial_history_ignores_every_not_later_position bound inputs claim position (notLater _ List.mem_cons_self)]
    exact ih (fun next member => notLater next (List.mem_cons_of_mem _ member))

theorem through_at_or_before_birth_is_the_original_initial_history (claim : Claim bound inputs)
    (count : Nat) (before : count ≤ claim.position.ordinal) : through bound inputs claim count = History.initial bound inputs claim := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [through, ih (by omega)]
    apply initial_fold
    intro position member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    unfold Later
    change ¬ (claim.position.ordinal < count ∨ (claim.position.ordinal = count ∧ claim.position.index.val < index.val))
    omega

theorem the_first_of_two_positions_is_the_complete_newborn_slice
    (claim : Claim bound inputs) (first second : Position bound inputs)
    (positions : positionsAt bound inputs first.ordinal = [first, second])
    (decoded : Mandate.Challenge.read bound inputs first = some claim) (secondEmpty : Mandate.Challenge.read bound inputs second = none) :
    claimsAt bound inputs first.ordinal = [claim] := by
  simp only [claimsAt, positions, List.filterMap_cons, decoded, secondEmpty, List.filterMap_nil]

theorem the_newborn_at_the_first_position_is_paid_terminal_at_the_second
    (claim : Claim bound inputs) (first second : Position bound inputs)
    (positions : positionsAt bound inputs first.ordinal = [first, second])
    (decoded : Mandate.Challenge.read bound inputs first = some claim) (secondEmpty : Mandate.Challenge.read bound inputs second = none)
    (attempt : Attempt bound inputs claim) (withdrawn : readAttempt bound inputs claim second = some attempt)
    (paid : (Mandate.law base scope).Valid (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request) :
    (through bound inputs claim (first.ordinal + 1)).isPending bound inputs = false := by
  have born := read_position bound inputs first claim decoded
  have prior := through_at_or_before_birth_is_the_original_initial_history bound inputs claim first.ordinal (by rw [born])
  have notLater : ¬ Later bound inputs claim.position first := by rw [born]; simp [Later]
  have unchanged := initial_history_ignores_every_not_later_position bound inputs claim first notLater
  have noRenew : readReconfirmation bound inputs claim second = none := by simp only [readReconfirmation, secondEmpty]
  rw [through, positions, prior, List.foldl_cons, unchanged, List.foldl_cons, List.foldl_nil]
  simp only [History.initial, History.receive, noRenew, Target.claim, withdrawn, dif_pos paid, History.isPending]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NewbornWithdrawal
