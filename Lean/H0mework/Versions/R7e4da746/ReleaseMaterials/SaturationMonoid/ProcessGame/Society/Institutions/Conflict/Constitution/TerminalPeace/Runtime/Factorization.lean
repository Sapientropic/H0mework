import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.FirstWrite
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Balance

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open ExposureGuard

noncomputable section

/-- The same dispatcher reserves the first recourse visit. All subsequent
proposals and arbitration are read from the raw scheduler. -/
def reserveInstallation (raw : WarScheduler) : WarScheduler where
  lane := fun tick past => match tick with | 0 => .personal | n + 1 => raw.lane n past
  personal := fun tick past => match tick with | 0 => stop | n + 1 => raw.personal n past
  rival := fun tick past => raw.rival (tick - 1) past
  offer := fun tick past tail => raw.offer (tick - 1) past tail

variable (answers : OwnerAnswers Original.seed) (raw : WarScheduler) (person : Bool)

def run (tick : Nat) : WarVisit :=
  (reserveInstallation raw).run answers person (damageGate Original.community)
    (fun _ _ => openProbe) opening tick

def afterInstallation (tick : Nat) : WarVisit :=
  raw.run answers person (damageGate Original.community) (fun _ _ => openProbe) (firstWrite answers) tick

theorem every_raw_history_uses_the_same_original_first_write (tick : Nat) :
    run answers raw person (tick + 1) = afterInstallation answers raw person tick := by
  induction tick with
  | zero => rfl
  | succ tick earlier =>
    unfold run afterInstallation at earlier ⊢
    rw [Scheduler.run, earlier, Scheduler.run]
    cases raw.lane tick
      (raw.run answers person (damageGate Original.community) (fun _ _ => openProbe) (firstWrite answers) tick).history <;> rfl

theorem every_arbitration_factors_through_the_same_protected_whole_state (tick : Nat) :
    run answers raw person (tick + 1) =
      raw.run answers person (damageGate Original.community) (fun _ _ => openProbe) protectedCut tick := by
  rw [every_raw_history_uses_the_same_original_first_write]
  unfold afterInstallation
  rw [every_installation_reaches_the_same_whole_protected_cut]

private theorem each_tick_extends_the_exact_original_prefix (tick : Nat) :
    (run answers raw person tick).history.IsPrefix (run answers raw person (tick + 1)).history := by
  unfold run
  rw [Scheduler.run]
  exact List.prefix_append _ _

theorem every_subsequent_history_has_its_unique_actual_suffix (tick : Nat) :
    ∃! tail : Original.Word,
      (run answers raw person (tick + 1)).history = protectedCut.history ++ tail := by
  rw [← every_installation_reaches_the_same_whole_protected_cut answers]
  have initial : (firstWrite answers).history.IsPrefix (run answers raw person (tick + 1)).history := by
    induction tick with
    | zero => rfl
    | succ tick prior =>
      exact prior.trans (each_tick_extends_the_exact_original_prefix answers raw person (tick + 1))
  obtain ⟨tail, exactHistory⟩ := initial
  refine ⟨tail, exactHistory.symm, fun other same => ?_⟩
  exact List.append_cancel_left (same.symm.trans exactHistory.symm)

theorem every_raw_attempt_after_the_installation_is_damage_free (tick : Nat) :
    let prior := run answers raw person (tick + 1)
    let requested := raw.proposal tick prior.history
    let selected := prior.verdict (raw.replies answers person tick prior.history)
      (damageGate Original.community) openProbe requested
    HEq (run answers raw person (tick + 2)).state
      (Receipts.writeAfter (raw.replies answers person tick prior.history) prior.state selected.emitted) ∧
    ∀ actual ∈ selected.emitted,
      Boundary.Actual.damages (endAt Original.seed prior.history) actual Original.community = [] := by
  let prior := run answers raw person (tick + 1)
  let votes := raw.replies answers person tick prior.history
  let requested := raw.proposal tick prior.history
  have successor : run answers raw person (tick + 2) = prior.step votes (damageGate Original.community) openProbe requested := by
    unfold run prior votes requested
    rw [Scheduler.run]
    cases raw.lane tick (run answers raw person (tick + 1)).history <;> rfl
  refine ⟨?_, fun actual written => selected_input_has_no_actual_damage _ actual written⟩
  rw [successor]
  rfl

theorem every_raw_history_retains_the_original_six_on_its_live_ledger (tick : Nat) :
    let current := run answers raw person tick
    current.state.stack.balances = [(Original.occurrence, Original.balance)] := by
  induction tick with
  | zero => exact Original.balances_exact
  | succ tick earlier =>
    unfold run at earlier ⊢
    dsimp only at earlier ⊢
    rw [Scheduler.run, the_revised_visit_keeps_the_exact_original_reparation_portfolio]
    exact earlier

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace
