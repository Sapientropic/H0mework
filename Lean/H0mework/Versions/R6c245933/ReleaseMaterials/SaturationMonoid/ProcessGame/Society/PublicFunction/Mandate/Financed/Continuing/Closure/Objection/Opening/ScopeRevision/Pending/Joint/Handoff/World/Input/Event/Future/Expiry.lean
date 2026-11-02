import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.ChallengeLine.Runtime
import Mathlib.Algebra.Order.Floor.Semiring

/-! The original source computes a finite expiry horizon. Clock passage
removes legitimate task authority without manufacturing a withdrawal receipt. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {scope : World.Scope} (bound : BoundSource base scope)

def horizon : Nat := ⌈scope.task.deadline - bound.source.seed.initial.clock⌉₊ + 1

theorem source_clock (inputs : List (List Action)) (ordinal : Nat) :
    (OutstandingSource.History.currentAt bound.source inputs ordinal).clock = bound.source.seed.initial.clock + ordinal := by
  induction ordinal with
  | zero => change bound.source.seed.initial.clock = bound.source.seed.initial.clock + (0 : ℚ); exact (add_zero _).symm
  | succ ordinal ih =>
    change (ProgrammeSource.rawCurrent (OutstandingSource.History.input bound.source inputs)
      (ProgrammeSource.next (OutstandingSource.History.input bound.source inputs)
        (ProgrammeHistory.visitAt (OutstandingSource.History.input bound.source inputs) ordinal).current)).clock = _
    rw [ProgrammeSource.actual_raw_next]
    change (bound.source.seed.law.next (OutstandingSource.History.currentAt bound.source inputs ordinal) _).clock = _
    rw [bound.law_exact]
    change (OutstandingSource.History.currentAt bound.source inputs ordinal).clock + max 0 (1 : ℚ) = _
    rw [ih]
    simp only [max_eq_right (by decide : (0 : ℚ) ≤ 1),Nat.cast_add,Nat.cast_one,add_assoc]

theorem horizon_expires (inputs : List (List Action)) (ordinal : Nat) (later : horizon bound ≤ ordinal) :
    scope.task.deadline < (OutstandingSource.History.currentAt bound.source inputs ordinal).clock := by
  rw [source_clock]
  have ceiling := Nat.le_ceil (scope.task.deadline - bound.source.seed.initial.clock)
  have large : (horizon bound : ℚ) ≤ ordinal := by exact_mod_cast later
  have step : (horizon bound : ℚ) = (⌈scope.task.deadline - bound.source.seed.initial.clock⌉₊ : ℚ) + 1 := by
    simp only [horizon,Nat.cast_add,Nat.cast_one]
  rw [step] at large
  linarith

private theorem step_clock (current : Current) (action : Action) :
    ((Mandate.law base scope).step current action).clock = current.clock := by
  unfold RawLaw.step
  split <;> rfl

private theorem item_clock (current : Current) (index : Nat) (word : List Action)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (member : item ∈ ((Mandate.law base scope).execute current index word).items) : item.before.clock = current.clock := by
  induction word generalizing current index with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons action tail ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same; rfl
    · exact (ih _ _ later).trans (step_clock _ _)

theorem every_later_actual_task_use_is_refused (inputs : List (List Action)) (ordinal : Nat)
    (later : horizon bound ≤ ordinal) (word : List Action)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (member : item ∈ (Mandate.law base scope).rawItems (OutstandingSource.History.currentAt bound.source inputs ordinal) word)
    (bearer : Bool) (goods : Bundle Good) (purpose : Use)
    (operation : item.request.operation = .use bearer goods purpose) (taskUse : Mandate.TaskUse scope item.request) :
    ¬ (Mandate.law base scope).Valid item.before item.request := by
  intro accepted
  have window := (Mandate.protected_use_requires_current_holder base scope _ _ bearer goods purpose operation taskUse accepted).2.2
  rw [item_clock _ 0 word item member] at window
  exact (not_lt_of_ge window) (horizon_expires bound inputs ordinal later)


theorem no_later_actual_proposal_acceptance_or_renewal (inputs : List (List Action)) (ordinal : Nat)
    (later : horizon bound ≤ ordinal) (word : List Action)
    (event : Mandate.ActualCommand base scope (OutstandingSource.History.currentAt bound.source inputs ordinal) word) :
    event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate := by
  have expired := horizon_expires bound inputs ordinal later
  have clock := item_clock (OutstandingSource.History.currentAt bound.source inputs ordinal) 0 word event.item.val event.item.property
  have permitted := event.authorization.2.2.2.2.2
  constructor
  · intro same
    rw [same] at permitted
    exact (not_lt_of_ge (clock ▸ permitted.2)) expired
  constructor
  · intro same
    rw [same] at permitted
    exact (not_lt_of_ge (clock ▸ permitted.2.2)) expired
  · intro candidate same
    rw [same] at permitted
    exact (not_lt_of_ge (clock ▸ permitted.2)) expired

variable {epoch : Epoch} (inventory : Inventory epoch) (depth : Nat)

def rootInput := Programme.Completion.I (Event.observed inventory (ChallengeLine.word inventory))
def rootInputs :=
  let attempt := Programme.Completion.Runtime.attempt (Event.observed inventory (ChallengeLine.word inventory))
  (Input.advance attempt.1 attempt.2).inputs

theorem root_input_is_the_original_executed_history :
    rootInput inventory = OutstandingSource.History.input epoch.bound.source (rootInputs inventory) := rfl

def actualExpiryEvent := OutstandingSource.History.actualExecution epoch.bound.source (rootInputs inventory) (horizon epoch.bound)

theorem actual_expiry_is_in_the_original_root :
    (actualExpiryEvent inventory).before = ProgrammeSource.rawCurrent (rootInput inventory)
      (ProgrammeHistory.visitAt (rootInput inventory) (horizon epoch.bound + 1)).current ∧
    epoch.scope.task.deadline < (actualExpiryEvent inventory).before.clock ∧
    ProgrammeSource.rawCurrent (rootInput inventory)
      (ProgrammeHistory.visitAt (rootInput inventory) (horizon epoch.bound + 1 + 1)).current = (actualExpiryEvent inventory).after := by
  refine ⟨rfl,horizon_expires epoch.bound (rootInputs inventory) _ (Nat.le_succ _),?_⟩
  change ProgrammeSource.rawCurrent (rootInput inventory)
    (ProgrammeSource.next (rootInput inventory) (ProgrammeHistory.visitAt (rootInput inventory) (horizon epoch.bound + 1)).current) = _
  rw [ProgrammeSource.actual_raw_next]
  exact (actualExpiryEvent inventory).after_exact.symm

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry
