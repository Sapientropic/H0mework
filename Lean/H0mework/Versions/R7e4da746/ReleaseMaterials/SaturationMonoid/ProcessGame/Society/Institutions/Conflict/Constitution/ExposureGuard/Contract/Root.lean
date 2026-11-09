import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Defence
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Exercise
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Retained
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Runtime.Trajectory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt inventory)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Raw" => RawCurrent Party Good M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

def start (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (seed : C) (community : Party → Community) (anchor : Word) (control : Raw → List Party)
    (exit : MandateExit.LiveAvailable seed anchor anchor community base scope control) :
    GuardedVisit base scope seed community anchor control :=
  Visit.start (Reparation.Actual.run seed community anchor)
    (Reparation.Actual.the_live_ledger_contains_exactly_the_original_losses seed community anchor)
    ⟨MandateExit.at_the_anchor_the_original_window_is_retained seed anchor, exit⟩

/-- Installation starts from a supplied native exit word and checks it
against the original pending window before opening the guarded route. -/
def install (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (seed : C) (community : Party → Community) (anchor : Word) (control : Raw → List Party)
    (word : Word) : MandateExit.LiveFailure seed anchor anchor community base scope control word ⊕
      GuardedVisit base scope seed community anchor control :=
  match MandateExit.inspectLive seed anchor anchor community base scope control word with
  | .inl issue => .inl issue
  | .inr selected => .inr (start base scope seed community anchor control ⟨word, selected.down⟩)

namespace Scheduler

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community} {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}
  (schedule : Scheduler Party Good Port (State Party Technology) Instrument)
  (answers : OwnerAnswers seed) (person : Party)
  (initial : GuardedVisit base scope seed community anchor control)

local notation "check" => exitProbe base scope seed community anchor control

abbrev guarded (tick : Nat) :=
  schedule.run answers person grantRule (fun i past => check (schedule.offer i past)) initial tick

/-- The live visit feeds its own selected history and complete original
ledger into the next visit. A newly reachable exit is checked there. -/
theorem every_guarded_visit_writes_the_original_ledger_and_keeps_an_independent_exit (tick : Nat) :
    let prior := schedule.guarded answers person initial tick
    let reply := schedule.replies answers person tick prior.history
    let input := schedule.proposal tick prior.history
    let emitted := (prior.decide reply (schedule.offer tick prior.history) input).emitted
    let reached := schedule.guarded answers person initial (tick + 1)
    Quantities.Recorded seed reached.history ∧
      reached.state = Receipts.writeAfter reply prior.state emitted ∧
      MandateExit.ReadyAt seed anchor reached.history community base scope control ∧
      ∀ loss ∈ Reparation.Actual.originalLosses seed community reached.history,
        ∃ balance, ∃ row, reached.state.read row = .inr (loss, balance) := by
  let reached := schedule.guarded answers person initial (tick + 1)
  exact ⟨Quantities.record _ _, rfl, reached.continues, reached.every_original_loss_has_an_exact_live_row⟩

theorem the_original_hard_expiry_survives_every_scheduled_successor
    (installed : Emergency.Installed seed base scope) (tick : Nat)
    (crossed : scope.task.deadline < (endAt seed (schedule.guarded answers person initial tick).history).raw.clock) :
    let reached := endAt seed (schedule.guarded answers person initial (tick + 1)).history
    Emergency.Installed reached base scope ∧ scope.task.deadline < reached.raw.clock ∧
      ∀ rawWord : RawEvent Party Good Port M Instrument, ∀ event : ActualCommand base scope reached.raw rawWord,
        event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate :=
  let prior := schedule.guarded answers person initial tick
  prior.a_visit_keeps_the_installed_original_hard_expiry (schedule.replies answers person tick prior.history)
    (schedule.offer tick prior.history) (schedule.proposal tick prior.history) installed crossed

/-- A single original exposed person can execute the same refusal at
every rival visit, regardless of the coalition's adaptive raw proposals. -/
theorem any_coalition_visit_preserves_original_refusal_stock_and_reparation
    (exposed : person ∈ bearers seed community anchor) (tick : Nat)
    (rival : schedule.lane tick (schedule.guarded answers person initial tick).history = .rival) :
    let prior := schedule.guarded answers person initial tick
    let reached := schedule.guarded answers person initial (tick + 1)
    (∀ good : Good, (endAt seed prior.history).raw.stock person good ≤ (endAt seed reached.history).raw.stock person good) ∧
      ∀ (loss : Reparation.Actual.Occurrence seed community) (balance : Reparation.Actual.Balance),
        loss.key.1 = person → (loss, balance) ∈ prior.state.stack.balances →
          ∃ row, reached.state.read row = .inr (loss, balance) := by
  exact ⟨fun good => schedule.any_adaptive_coalition_visit_preserves_the_refusing_bearers_stock
    answers person grantRule (fun i past => check (schedule.offer i past)) initial exposed tick good rival,
    fun loss balance same old => schedule.any_adaptive_coalition_visit_preserves_the_refusing_victims_reparation
      answers person grantRule (fun i past => check (schedule.offer i past)) initial tick loss balance same old rival⟩

theorem a_coalition_visit_cannot_install_any_grant_with_an_original_refusal
    (exposed : person ∈ bearers seed community anchor) (tick : Nat)
    (rival : schedule.lane tick (schedule.guarded answers person initial tick).history = .rival) :
    let prior := schedule.guarded answers person initial tick
    let reply := schedule.replies answers person tick prior.history
    let input := schedule.proposal tick prior.history
    ∀ item ∈ inventory (endAt seed prior.history) (prior.decide reply (schedule.offer tick prior.history) input).emitted, ¬ Grants item.request := by
  let prior := schedule.guarded answers person initial tick
  have selected := schedule.rival_inputs answers person tick prior.history rival
  change ∀ item ∈ inventory (endAt seed prior.history)
    (prior.decide (schedule.replies answers person tick prior.history) (schedule.offer tick prior.history)
      (schedule.proposal tick prior.history)).emitted, _
  rw [selected.1, selected.2]
  exact prior.a_rival_visit_has_no_new_grant_for_any_withholding_bearer answers
    (schedule.offer tick prior.history) (schedule.rival tick prior.history) (List.mem_append_left _ exposed)

private theorem original_release_persists_without_any_paid_grant
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed initial.history).raw)
    (tick : Nat) (without : ∀ i < tick,
      let prior := schedule.guarded answers person initial i
      let reply := schedule.replies answers person i prior.history
      let input := schedule.proposal i prior.history
      ∀ item ∈ inventory (endAt seed prior.history) (prior.decide reply (schedule.offer i prior.history) input).emitted, ¬ Grants item.request) :
    Civil.Mandate.Released (endAt seed (schedule.guarded answers person initial tick).history).raw := by
  induction tick with
  | zero => exact released
  | succ tick earlier =>
    let prior := schedule.guarded answers person initial tick
    have closed := earlier (fun i before => without i (Nat.lt_succ_of_lt before))
    exact prior.a_visit_with_no_new_grant_keeps_original_release
      (schedule.replies answers person tick prior.history) (schedule.offer tick prior.history)
      (schedule.proposal tick prior.history) installed closed
      (without tick (Nat.lt_succ_self tick))

theorem no_coalition_restores_the_original_authority_at_any_rival_prefix
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed initial.history).raw)
    (exposed : person ∈ bearers seed community anchor) (tick : Nat)
    (rival : ∀ i < tick, schedule.lane i (schedule.guarded answers person initial i).history = .rival) :
    Civil.Mandate.Released (endAt seed (schedule.guarded answers person initial tick).history).raw :=
  schedule.original_release_persists_without_any_paid_grant answers person initial installed released tick
    (fun i earlier => schedule.a_coalition_visit_cannot_install_any_grant_with_an_original_refusal answers person initial
      exposed i (rival i earlier))

/-- A return of either slot has a literal grant visit with the original
bearer's affirmative input, even when personal and rival inputs interleave. -/
theorem any_revival_reveals_a_personal_approval_at_the_original_grant_item
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed initial.history).raw)
    (exposed : person ∈ bearers seed community anchor) (tick : Nat)
    (revived : ¬ Civil.Mandate.Released (endAt seed (schedule.guarded answers person initial tick).history).raw) :
    ∃ i < tick,
      let prior := schedule.guarded answers person initial i
      let reply := schedule.replies answers person i prior.history
      let input := schedule.proposal i prior.history
      schedule.lane i prior.history = .personal ∧
      ∃ actual ∈ (prior.decide reply (schedule.offer i prior.history) input).emitted,
        ∃ position : Fin (originalItems (seed := seed) prior.history actual).length,
          Grants (originalItems (seed := seed) prior.history actual)[position].request ∧
            answers prior.history actual position person = true := by
  classical
  by_contra noApproval
  apply revived
  apply schedule.original_release_persists_without_any_paid_grant answers person initial installed released tick
  intro i earlier prior reply input item listed grant
  have lane : schedule.lane i prior.history = .personal := by
    cases chosen : schedule.lane i prior.history
    · rfl
    · exact (schedule.a_coalition_visit_cannot_install_any_grant_with_an_original_refusal
        answers person initial exposed i chosen item listed grant).elim
  have replyExact : reply = answers := by
    unfold reply replies
    rw [lane]
  obtain ⟨actual, chosen, position, same, authorized⟩ :=
    (prior.decide reply (schedule.offer i prior.history) input).a_written_grant_reads_each_original_bearer
      (List.mem_append_left _ exposed) item listed grant
  rw [replyExact] at authorized
  exact noApproval ⟨i, earlier, lane, actual, chosen, position, by rwa [same], authorized⟩

end Scheduler

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
