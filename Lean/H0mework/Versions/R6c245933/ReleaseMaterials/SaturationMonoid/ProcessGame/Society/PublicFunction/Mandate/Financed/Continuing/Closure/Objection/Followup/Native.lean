import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable (fuel : ℚ) (inputs : List (List Action))

def tracked (original : Claim fuel inputs) (target : Target fuel inputs original) : AdmittedObligation (V fuel inputs) :=
  { obligation fuel inputs original with residual := (target.claim fuel inputs).snapshot fuel inputs }

inductive Boundary (original : Claim fuel inputs) (obligation : AdmittedObligation (V fuel inputs))
  | inherited (event : Objection.Boundary fuel inputs original obligation)
  | reaffirm (previous : Target fuel inputs original) (receipt : Reconfirmation fuel inputs original)
      (later : Later fuel inputs (previous.claim fuel inputs).position receipt.target.position)
      (exact : obligation = tracked fuel inputs original previous)
  | attempt (target : Target fuel inputs original) (receipt : Attempt fuel inputs (target.claim fuel inputs))
      (exact : obligation = tracked fuel inputs original target)

def Boundary.source {original : Claim fuel inputs} {obligation : AdmittedObligation (V fuel inputs)} :
    Boundary fuel inputs original obligation → Event fuel inputs
  | .inherited event => .attempt original event.attempt
  | .reaffirm previous receipt _ _ => .reaffirmed original previous receipt
  | .attempt target receipt _ => .trackedAttempt original target receipt

def disposition (original : Claim fuel inputs) {obligation : AdmittedObligation (V fuel inputs)}
    (event : Boundary fuel inputs original obligation) : BoundaryDisposition (V fuel inputs) obligation event.source := by
  cases event with
  | inherited event => exact Objection.disposition fuel inputs original event
  | reaffirm previous receipt later exact =>
      subst obligation
      exact .carry (.progressed (receipt.target.snapshot fuel inputs) ⟨rfl, rfl, rfl, later⟩)
  | attempt target receipt exact =>
      subst obligation
      if accepted : law.Valid (receipt.position.item fuel inputs).before (receipt.position.item fuel inputs).request then
        exact .terminal (.final (.fulfilled (.inr (.inl ⟨rfl, rfl, accepted⟩))))
      else exact .carry (.deferred (.inr (.inl ⟨rfl, rfl, accepted⟩)))

def process (original : Claim fuel inputs) : NativeResponsibilityProcess (V fuel inputs) where
  AdmissionEvent := Unit
  admissionPayload := fun _ => admission fuel inputs original
  BoundaryEvent := Boundary fuel inputs original
  boundarySource := Boundary.source fuel inputs
  boundary_anchor_eq := fun event => by
    cases event with
    | inherited event => exact (Objection.process fuel inputs original).boundary_anchor_eq event
    | reaffirm previous receipt later exact => subst_vars; rfl
    | attempt target receipt exact => subst_vars; rfl
  boundary_incidence_eq := fun event => by
    cases event with
    | inherited event => exact (Objection.process fuel inputs original).boundary_incidence_eq event
    | reaffirm previous receipt later exact => subst_vars; rfl
    | attempt target receipt exact => subst_vars; rfl
  boundaryDisposition := disposition fuel inputs original
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

/-- The original run is embedded edge for edge; no new admission is replayed. -/
def inheritRun (original : Claim fuel inputs) {source target : ResponsibilityState (V fuel inputs)} :
    (Objection.process fuel inputs original).Run source target → (process fuel inputs original).Run source target
  | .nil => .nil
  | .step prior (.admit event) => .step (inheritRun original prior) (.admit event)
  | .step prior (.cross slot obligation present event) =>
      .step (inheritRun original prior) (.cross slot obligation present (.inherited event))
  | .step _ (.reopen _ _ _ impossible) => nomatch impossible

def inheritState (original : Claim fuel inputs) (state : (Objection.process fuel inputs original).GeneratedState) :
    (process fuel inputs original).GeneratedState := ⟨state.current, inheritRun fuel inputs original state.generated⟩

theorem inheritRun_events (original : Claim fuel inputs) {source target : ResponsibilityState (V fuel inputs)}
    (run : (Objection.process fuel inputs original).Run source target) :
    (inheritRun fuel inputs original run).events = run.events := by
  induction run with
  | nil => rfl
  | step prior edge ih =>
    cases edge with
    | admit event =>
      simp only [inheritRun, NativeResponsibilityProcess.Run.events]
      rw [ih]
      rfl
    | cross slot obligation present event =>
      simp only [inheritRun, NativeResponsibilityProcess.Run.events]
      rw [ih]
      rfl
    | reopen slot archive present impossible => exact nomatch impossible

inductive History (original : Claim fuel inputs)
  | pending (target : Target fuel inputs original) (state : (process fuel inputs original).GeneratedState)
      (slots : state.current.slots = [.live (tracked fuel inputs original target)])
  | closed (state : (process fuel inputs original).GeneratedState) (archive : TerminalArchive (V fuel inputs))
      (slots : state.current.slots = [.terminal archive])

def History.state {original : Claim fuel inputs} : History fuel inputs original → (process fuel inputs original).GeneratedState
  | .pending _ state _ | .closed state _ _ => state

def History.isPending {original : Claim fuel inputs} : History fuel inputs original → Bool
  | .pending .. => true | .closed .. => false

def History.inherit {original : Claim fuel inputs} : Objection.History fuel inputs original → History fuel inputs original
  | .pending state slots => .pending .initial (inheritState fuel inputs original state) slots
  | .closed state archive slots => .closed (inheritState fuel inputs original state) archive slots

def History.receive {original : Claim fuel inputs} (history : History fuel inputs original) (position : Position fuel inputs) :
    History fuel inputs original := by
  cases history with
  | closed state archive slots => exact .closed state archive slots
  | pending target state slots =>
    let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
    have present : state.current.slots.get address = .live (tracked fuel inputs original target) := by simp [slots, address]
    match readReconfirmation fuel inputs original position with
    | some receipt =>
      if later : Later fuel inputs (target.claim fuel inputs).position receipt.target.position then
        let event : Boundary fuel inputs original (tracked fuel inputs original target) := .reaffirm target receipt later rfl
        let edge : (process fuel inputs original).Edge state.current := .cross address _ present event
        exact .pending (.renewed receipt) (state.step (process fuel inputs original) edge) (by
          simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
            process, disposition, slots, event, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target, tracked, Target.claim])
      else exact .pending target state slots
    | none =>
      match readAttempt fuel inputs (target.claim fuel inputs) position with
      | none => exact .pending target state slots
      | some receipt =>
        let event : Boundary fuel inputs original (tracked fuel inputs original target) := .attempt target receipt rfl
        let edge : (process fuel inputs original).Edge state.current := .cross address _ present event
        if accepted : law.Valid (receipt.position.item fuel inputs).before (receipt.position.item fuel inputs).request then
          exact .closed (state.step (process fuel inputs original) edge)
            ⟨tracked fuel inputs original target, .trackedAttempt original target receipt, .fulfilled (.inr (.inl ⟨rfl, rfl, accepted⟩))⟩ (by
              simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
                process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot, Boundary.source])
        else
          exact .pending target (state.step (process fuel inputs original) edge) (by
            simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
              process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])

def through (original : Claim fuel inputs) : Nat → History fuel inputs original
  | 0 => History.inherit fuel inputs (Objection.History.initial fuel inputs original)
  | ordinal + 1 => (positionsAt fuel inputs ordinal).foldl (History.receive fuel inputs) (through original ordinal)

theorem inherited_current_is_literal (original : Claim fuel inputs) (state : (Objection.process fuel inputs original).GeneratedState) :
    (inheritState fuel inputs original state).current = state.current := rfl

theorem retarget_preserves_original_responsibility (original : Claim fuel inputs) (target : Target fuel inputs original) :
    (tracked fuel inputs original target).admission = (obligation fuel inputs original).admission ∧
    (tracked fuel inputs original target).bearer = original.actor fuel inputs ∧
    (tracked fuel inputs original target).content = original ∧
    (tracked fuel inputs original target).scope = original.origin fuel inputs ∧
    (tracked fuel inputs original target).lineage = original.origin fuel inputs := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem actual_native_history (original : Claim fuel inputs) (count : Nat) :
    (through fuel inputs original count).state.current.history =
      (through fuel inputs original count).state.generated.events := (through fuel inputs original count).state.history_eq

theorem tracked_fulfilled_has_actual_withdrawal (event : Event fuel inputs) (original : Claim fuel inputs)
    (origin : Financial.InstructionOrigin (I fuel inputs))
    (receipt : Event.TrackedResolvedAt fuel inputs event original origin) :
    ∃ (target : Target fuel inputs original) (attempt : Attempt fuel inputs (target.claim fuel inputs)),
      event = .trackedAttempt original target attempt ∧
      (target.claim fuel inputs).actor fuel inputs = original.actor fuel inputs ∧
      law.Valid (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request ∧
      (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.holder = none ∧
      (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.offered = none ∧
      (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.version =
        ((target.claim fuel inputs).snapshot fuel inputs).version + 1 := by
  cases event with
  | birth claim => exact nomatch receipt
  | attempt claim attempt => exact nomatch receipt
  | reaffirmed claim previous renewed => exact nomatch receipt
  | crossReaffirm claim actualInputs previous renewed => exact nomatch receipt
  | crossAttempt claim actualInputs target attempt => exact nomatch receipt
  | trackedAttempt claim target attempt =>
      rcases receipt with ⟨rfl, _, accepted⟩
      exact ⟨target, attempt, rfl, target.actor fuel inputs, accepted,
        attempt.actual_withdrawal fuel inputs (target.claim fuel inputs) accepted⟩

-- Independent consumers must share the equation declaration from this owner.
attribute [local simp] History.receive.eq_1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup
