import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Followup

variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : Ready inventory)

def refusedRequest : Action := ⟨ready.actor, [], .service, [.service], .present⟩

theorem original_request_is_really_refused :
    ¬ (epochLaw ready).Valid ((epochLaw ready).next (epochInitial ready) []) (refusedRequest ready) := by
  intro accepted
  have permission := accepted.2.1 .service (by simp [refusedRequest, RawLaw.requiredPorts, RawLaw.debit])
  rcases permission with permitted | consent
  · have noHolder : ((epochLaw ready).next (epochInitial ready) []).technology.holder = none := ready.quiet.1
    change decide (((epochLaw ready).next (epochInitial ready) []).technology.holder = some ready.actor) = true at permitted
    have hasHolder := of_decide_eq_true permitted
    rw [noHolder] at hasHolder
    cases hasHolder
  · exact List.not_mem_nil consent

def epochSource : OutstandingSource Bool Good Mandate.Source.Port (State Bool Unit) Unit where
  seed := {
    law := epochLaw ready
    initial := epochInitial ready
    task := ready.task
    actionsAt := fun current => epochWord ready current
    budget := 0
    original := [refusedRequest ready]
    refused := ⟨⟨0, (epochLaw ready).next (epochInitial ready) [], refusedRequest ready⟩,
      List.mem_cons_self, original_request_is_really_refused ready⟩ }
  positive := by
    intro slot inside
    obtain ⟨actor, _, member⟩ := List.mem_flatMap.mp inside
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨(.service, 1), by simp, by decide⟩

def epochBefore := (epochSource ready).canonicalPrefix 2 |>.frame.raw
def epochInputs := [epochWord ready (epochBefore ready)]
def epochBound : BoundSource base ready.scope := ⟨epochSource ready, rfl⟩
def epochInput := OutstandingSource.History.input (epochSource ready) (epochInputs ready)

abbrev epochCurrent (ordinal : Nat) := OutstandingSource.History.currentAt (epochSource ready) (epochInputs ready) ordinal
abbrev epochExecution := OutstandingSource.History.actualExecution (epochSource ready) (epochInputs ready) 1

theorem the_new_source_initial_is_the_actual_old_successor :
    (epochInput ready).initial = (advance inventory).cut.past.frame.raw := rfl

theorem generated_word_is_actually_emitted : (epochExecution ready).submitted = epochWord ready (epochBefore ready) :=
  OutstandingSource.History.scheduled_input_is_actual (epochSource ready) (epochInputs ready) 0 (by simp [epochInputs])

theorem generated_word_uses_its_actual_before : (epochExecution ready).before = epochBefore ready := by
  apply (OutstandingSource.History.actual_frame (epochSource ready) (epochInputs ready) 2).1.trans
  exact congrArg (fun past => past.frame.raw)
    (OutstandingSource.History.finite_prefix_exact (epochSource ready) (epochInputs ready) 0 (Nat.zero_le _))

theorem generated_word_has_its_own_actual_after :
    epochCurrent ready 3 = (epochLaw ready).next (epochBefore ready) (epochWord ready (epochBefore ready)) := by
  change OutstandingSource.History.currentAt (epochSource ready) (epochInputs ready) 3 = _
  rw [← OutstandingSource.History.actual_next (epochSource ready) (epochInputs ready) 1]
  change (epochLaw ready).next (epochExecution ready).before (epochExecution ready).submitted = _
  rw [generated_word_is_actually_emitted ready, generated_word_uses_its_actual_before ready]

inductive EpochOutcome where
  | private paid (payment : Paid ready (epochBefore ready)) (selected : select ready (epochBefore ready) = some payment)
      (actual : (∀ item ∈ (epochLaw ready).rawItems (epochExecution ready).before (epochExecution ready).submitted,
        (epochLaw ready).Valid item.before item.request) ∧
        ServiceAdequate (epochLaw ready) (epochExecution ready).before ready.task (epochExecution ready).submitted)
  | private blocked (absent : select ready (epochBefore ready) = none)
      (failures : ∀ method ∈ methods, ¬ Pass ready (epochBefore ready) method)
      (actual_failure : ¬ ((∀ item ∈ (epochLaw ready).rawItems (epochExecution ready).before
        (epochExecution ready).submitted, (epochLaw ready).Valid item.before item.request) ∧
        ServiceAdequate (epochLaw ready) (epochExecution ready).before ready.task (epochExecution ready).submitted))

def epochOutcome : EpochOutcome ready :=
  match selected : select ready (epochBefore ready) with
  | some paid => .paid paid selected (by
      rw [generated_word_is_actually_emitted, generated_word_uses_its_actual_before]
      exact selected_word_really_pays_the_generated_task ready _ paid selected)
  | none => .blocked selected (blocked_menu_has_concrete_failed_checks ready _ selected) (by
      rw [generated_word_is_actually_emitted, generated_word_uses_its_actual_before]
      change ¬ Pass ready (epochBefore ready) _
      simp only [selected, Option.map_none, Option.getD_none]
      exact blocked_menu_has_concrete_failed_checks ready _ selected .productive (by simp [methods]))

abbrev epochServices (index : (epochSource ready).Slot) :=
  OutstandingSource.History.NativeService.historyAt (epochSource ready) (epochInputs ready) index 2

def newGrants := grantsAt base ready.scope
  (Mandate.History.Runtime.currentAt (epochBound ready) (epochInputs ready) 1)
  (Mandate.History.Runtime.wordAt (epochBound ready) (epochInputs ready) 1)

structure TracedGrant where
  private mk ::
  admission : AdmittedGrant base ready.scope
    (Mandate.History.Runtime.currentAt (epochBound ready) (epochInputs ready) 1)
    (Mandate.History.Runtime.wordAt (epochBound ready) (epochInputs ready) 1)
  history : Lifecycle.Observed.History base ready.scope
    (Mandate.History.Runtime.currentAt (epochBound ready) (epochInputs ready))
    (Mandate.History.Runtime.wordAt (epochBound ready) (epochInputs ready)) 1 admission.grant
  exact : history = Lifecycle.Observed.through 1

def grantRecords : List (TracedGrant ready) := (newGrants ready).map fun grant =>
  ⟨admitGrant base ready.scope _ _ grant, Lifecycle.Observed.through 1, rfl⟩

theorem every_generated_scope_grant_retains_its_live_original_admission (record : TracedGrant ready) :
    record.history.state.LiveAt 0 ∧
    HEq record.history.obligation.admission
      (Lifecycle.original base ready.scope
        (Mandate.History.Runtime.currentAt (epochBound ready) (epochInputs ready))
        (Mandate.History.Runtime.wordAt (epochBound ready) (epochInputs ready)) 1 record.admission.grant).admission :=
  ⟨record.history.responsibility_remains_live, record.history.original_admission⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision
