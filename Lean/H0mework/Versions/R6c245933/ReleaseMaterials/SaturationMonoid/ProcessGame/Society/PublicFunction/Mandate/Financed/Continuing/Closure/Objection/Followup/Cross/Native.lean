import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {fuel : ℚ} {originInputs : List (List Action)}

def tracked {original : Claim fuel originInputs} {inputs : List (List Action)} (target : Target original inputs) :
    AdmittedObligation (V fuel originInputs) :=
  { obligation fuel originInputs original with residual := target.snapshot }

inductive Boundary (original : Claim fuel originInputs) (obligation : AdmittedObligation (V fuel originInputs))
  | inherited (event : Followup.Boundary fuel originInputs original obligation)
  | reaffirm {inputs : List (List Action)} (target : Target original inputs) (receipt : Reconfirmation target)
      (exact : obligation = tracked target)
  | attempt {inputs : List (List Action)} (target : Target original inputs) (receipt : Attempt fuel inputs target.claim)
      (exact : obligation = tracked target)

def Boundary.source {original : Claim fuel originInputs} {obligation : AdmittedObligation (V fuel originInputs)} :
    Boundary original obligation → Event fuel originInputs
  | .inherited event => event.source fuel originInputs
  | .reaffirm target receipt _ => .crossReaffirm original _ target receipt
  | .attempt target receipt _ => .crossAttempt original _ target receipt

def disposition (original : Claim fuel originInputs) {obligation : AdmittedObligation (V fuel originInputs)}
    (event : Boundary original obligation) : BoundaryDisposition (V fuel originInputs) obligation event.source := by
  cases event with
  | inherited event => exact Followup.disposition fuel originInputs original event
  | reaffirm target receipt exact =>
      subst obligation
      exact .carry (.progressed receipt.target.snapshot ⟨rfl, rfl, rfl⟩)
  | attempt target receipt exact =>
      subst obligation
      if accepted : law.Valid (receipt.position.item fuel _).before (receipt.position.item fuel _).request then
        exact .terminal (.final (.fulfilled (.inr (.inr ⟨rfl, rfl, accepted⟩))))
      else exact .carry (.deferred (.inr (.inr ⟨rfl, rfl, accepted⟩)))

def process (original : Claim fuel originInputs) : NativeResponsibilityProcess (V fuel originInputs) where
  AdmissionEvent := Unit
  admissionPayload := fun _ => admission fuel originInputs original
  BoundaryEvent := Boundary original
  boundarySource := Boundary.source
  boundary_anchor_eq := fun event => by
    cases event with
    | inherited event => exact (Followup.process fuel originInputs original).boundary_anchor_eq event
    | reaffirm target receipt exact => subst_vars; rfl
    | attempt target receipt exact => subst_vars; rfl
  boundary_incidence_eq := fun event => by
    cases event with
    | inherited event => exact (Followup.process fuel originInputs original).boundary_incidence_eq event
    | reaffirm target receipt exact => subst_vars; rfl
    | attempt target receipt exact => subst_vars; rfl
  boundaryDisposition := disposition original
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def inheritRun (original : Claim fuel originInputs) {source target : ResponsibilityState (V fuel originInputs)} :
    (Followup.process fuel originInputs original).Run source target → (process original).Run source target
  | .nil => .nil
  | .step prior (.admit event) => .step (inheritRun original prior) (.admit event)
  | .step prior (.cross slot obligation present event) =>
      .step (inheritRun original prior) (.cross slot obligation present (.inherited event))
  | .step _ (.reopen _ _ _ impossible) => nomatch impossible

def inheritState (original : Claim fuel originInputs) (state : (Followup.process fuel originInputs original).GeneratedState) :
    (process original).GeneratedState := ⟨state.current, inheritRun original state.generated⟩

theorem inheritRun_events (original : Claim fuel originInputs) {source target : ResponsibilityState (V fuel originInputs)}
    (run : (Followup.process fuel originInputs original).Run source target) : (inheritRun original run).events = run.events := by
  induction run with
  | nil => rfl
  | step prior edge ih =>
    cases edge with
    | admit event => simp only [inheritRun, NativeResponsibilityProcess.Run.events]; rw [ih]; rfl
    | cross slot obligation present event => simp only [inheritRun, NativeResponsibilityProcess.Run.events]; rw [ih]; rfl
    | reopen slot archive present impossible => exact nomatch impossible

inductive History (original : Claim fuel originInputs) (inputs : List (List Action))
  | pending (target : Target original inputs) (state : (process original).GeneratedState)
      (slots : state.current.slots = [.live (tracked target)])
  | closed (state : (process original).GeneratedState) (archive : TerminalArchive (V fuel originInputs))
      (slots : state.current.slots = [.terminal archive])

def History.state {original : Claim fuel originInputs} {inputs : List (List Action)} :
    History original inputs → (process original).GeneratedState
  | .pending _ state _ | .closed state _ _ => state

def History.isPending {original : Claim fuel originInputs} {inputs : List (List Action)} : History original inputs → Bool
  | .pending .. => true | .closed .. => false

def History.inherit {original : Claim fuel originInputs} : Followup.History fuel originInputs original → History original originInputs
  | .pending target state slots => by
      cases target with
      | initial => exact .pending (Target.local .initial) (inheritState original state) slots
      | renewed receipt => exact .pending (Target.local (.renewed receipt)) (inheritState original state) slots
  | .closed state archive slots => .closed (inheritState original state) archive slots

def History.receive {original : Claim fuel originInputs} {inputs : List (List Action)}
    (history : History original inputs) (position : Position fuel inputs) : History original inputs := by
  cases history with
  | closed state archive slots => exact .closed state archive slots
  | pending target state slots =>
    let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
    have present : state.current.slots.get address = .live (tracked target) := by simp [slots, address]
    match readReconfirmation target position with
    | some receipt =>
      let event : Boundary original (tracked target) := .reaffirm target receipt rfl
      let edge : (process original).Edge state.current := .cross address _ present event
      exact .pending receipt.target (state.step (process original) edge) (by
        simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
          process, disposition, slots, event, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target, tracked])
    | none =>
      match readAttempt fuel inputs target.claim position with
      | none => exact .pending target state slots
      | some receipt =>
        let event : Boundary original (tracked target) := .attempt target receipt rfl
        let edge : (process original).Edge state.current := .cross address _ present event
        if accepted : law.Valid (receipt.position.item fuel inputs).before (receipt.position.item fuel inputs).request then
          exact .closed (state.step (process original) edge)
            ⟨tracked target, .crossAttempt original inputs target receipt, .fulfilled (.inr (.inr ⟨rfl, rfl, accepted⟩))⟩ (by
              simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
                process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot, Boundary.source])
        else
          exact .pending target (state.step (process original) edge) (by
            simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
              process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])

theorem old_admission_and_actor_are_literal {original : Claim fuel originInputs} {inputs : List (List Action)}
    (target : Target original inputs) :
    (tracked target).admission = (obligation fuel originInputs original).admission ∧
    (tracked target).bearer = original.actor fuel originInputs ∧
    (tracked target).content = original ∧ (tracked target).residual = target.snapshot := ⟨rfl, rfl, rfl, rfl⟩

-- Independent consumers must share the equation declaration from this owner.
attribute [local simp] History.receive.eq_1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross
