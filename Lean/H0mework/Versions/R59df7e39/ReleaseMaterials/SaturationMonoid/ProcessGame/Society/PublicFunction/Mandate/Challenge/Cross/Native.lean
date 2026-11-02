import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type}
  (bound : ProgrammeFamily base scope Index)
  {originInputs : Index}

def tracked {original : Claim bound originInputs} {inputs : Index} (target : Target bound original inputs) :
    AdmittedObligation (V bound originInputs) :=
  { obligation bound originInputs original with residual := target.snapshot bound }

inductive Boundary (original : Claim bound originInputs) (obligation : AdmittedObligation (V bound originInputs))
  | inherited (event : Challenge.Boundary bound originInputs original obligation)
  | reaffirm {inputs : Index} (target : Target bound original inputs) (receipt : Reconfirmation bound target)
      (exact : obligation = tracked bound target)
  | attempt {inputs : Index} (target : Target bound original inputs) (receipt : Attempt bound inputs target.claim)
      (exact : obligation = tracked bound target)

def Boundary.source {original : Claim bound originInputs} {obligation : AdmittedObligation (V bound originInputs)} :
    Boundary bound original obligation → Event bound originInputs
  | .inherited event => event.source bound originInputs
  | .reaffirm target receipt _ => .remoteReaffirm original _ target receipt
  | .attempt target receipt _ => .remoteAttempt original _ target receipt

def disposition (original : Claim bound originInputs) {obligation : AdmittedObligation (V bound originInputs)}
    (event : Boundary bound original obligation) : BoundaryDisposition (V bound originInputs) obligation event.source := by
  cases event with
  | inherited event => exact Challenge.disposition bound originInputs original event
  | reaffirm target receipt exact =>
      subst obligation
      exact .carry (.progressed ((receipt.target bound).snapshot bound) ⟨rfl, rfl, rfl⟩)
  | attempt target receipt exact =>
      subst obligation
      if accepted : (law base scope).Valid (receipt.position.item bound _).before (receipt.position.item bound _).request then
        exact .terminal (.final (.fulfilled (.inr ⟨rfl, rfl, accepted⟩)))
      else exact .carry (.deferred (.inr ⟨rfl, rfl, accepted⟩))

def process (original : Claim bound originInputs) : NativeResponsibilityProcess (V bound originInputs) where
  AdmissionEvent := Unit
  admissionPayload := fun _ => admission bound originInputs original
  BoundaryEvent := Boundary bound original
  boundarySource := Boundary.source bound
  boundary_anchor_eq := fun event => by
    cases event with
    | inherited event => exact (Challenge.process bound originInputs original).boundary_anchor_eq event
    | reaffirm target receipt exact => subst_vars; rfl
    | attempt target receipt exact => subst_vars; rfl
  boundary_incidence_eq := fun event => by
    cases event with
    | inherited event => exact (Challenge.process bound originInputs original).boundary_incidence_eq event
    | reaffirm target receipt exact => subst_vars; rfl
    | attempt target receipt exact => subst_vars; rfl
  boundaryDisposition := disposition bound original
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def inheritRun (original : Claim bound originInputs) {source target : ResponsibilityState (V bound originInputs)} :
    (Challenge.process bound originInputs original).Run source target → (process bound original).Run source target
  | .nil => .nil
  | .step prior (.admit event) => .step (inheritRun original prior) (.admit event)
  | .step prior (.cross slot obligation present event) =>
      .step (inheritRun original prior) (.cross slot obligation present (.inherited event))
  | .step _ (.reopen _ _ _ impossible) => nomatch impossible

def inheritState (original : Claim bound originInputs) (state : (Challenge.process bound originInputs original).GeneratedState) :
    (process bound original).GeneratedState := ⟨state.current, inheritRun bound original state.generated⟩

theorem inheritRun_events (original : Claim bound originInputs) {source target : ResponsibilityState (V bound originInputs)}
    (run : (Challenge.process bound originInputs original).Run source target) : (inheritRun bound original run).events = run.events := by
  induction run with
  | nil => rfl
  | step prior edge ih =>
    cases edge with
    | admit event => simp only [inheritRun, NativeResponsibilityProcess.Run.events]; rw [ih]; rfl
    | cross slot obligation present event => simp only [inheritRun, NativeResponsibilityProcess.Run.events]; rw [ih]; rfl
    | reopen slot archive present impossible => exact nomatch impossible

inductive History (original : Claim bound originInputs) (inputs : Index)
  | pending (target : Target bound original inputs) (state : (process bound original).GeneratedState)
      (slots : state.current.slots = [.live (tracked bound target)])
  | closed (state : (process bound original).GeneratedState) (archive : TerminalArchive (V bound originInputs))
      (slots : state.current.slots = [.terminal archive])

def History.state {original : Claim bound originInputs} {inputs : Index} :
    History bound original inputs → (process bound original).GeneratedState
  | .pending _ state _ | .closed state _ _ => state

def History.isPending {original : Claim bound originInputs} {inputs : Index} : History bound original inputs → Bool
  | .pending .. => true | .closed .. => false

def History.inherit {original : Claim bound originInputs} : Challenge.History bound originInputs original → History bound original originInputs
  | .pending target state slots => by
      cases target with
      | initial => exact .pending (Target.local bound .initial) (inheritState bound original state) slots
      | renewed receipt => exact .pending (Target.local bound (.renewed receipt)) (inheritState bound original state) slots
  | .closed state archive slots => .closed (inheritState bound original state) archive slots

def History.receive {original : Claim bound originInputs} {inputs : Index}
    (history : History bound original inputs) (position : Position bound inputs) : History bound original inputs := by
  cases history with
  | closed state archive slots => exact .closed state archive slots
  | pending target state slots =>
    let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
    have present : state.current.slots.get address = .live (tracked bound target) := by simp [slots, address]
    match readReconfirmation bound target position with
    | some receipt =>
      let event : Boundary bound original (tracked bound target) := .reaffirm target receipt rfl
      let edge : (process bound original).Edge state.current := .cross address _ present event
      exact .pending (receipt.target bound) (state.step (process bound original) edge) (by
        simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
          process, disposition, slots, event, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target, tracked])
    | none =>
      match readAttempt bound inputs target.claim position with
      | none => exact .pending target state slots
      | some receipt =>
        let event : Boundary bound original (tracked bound target) := .attempt target receipt rfl
        let edge : (process bound original).Edge state.current := .cross address _ present event
        if accepted : (law base scope).Valid (receipt.position.item bound inputs).before (receipt.position.item bound inputs).request then
          exact .closed (state.step (process bound original) edge)
            ⟨tracked bound target, .remoteAttempt original inputs target receipt, .fulfilled (.inr ⟨rfl, rfl, accepted⟩)⟩ (by
              simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
                process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot, Boundary.source])
        else
          exact .pending target (state.step (process bound original) edge) (by
            simp [edge, NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
              process, disposition, accepted, slots, event, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])

theorem old_admission_and_actor_are_literal {original : Claim bound originInputs} {inputs : Index}
    (target : Target bound original inputs) :
    (tracked bound target).admission = (obligation bound originInputs original).admission ∧
    (tracked bound target).bearer = original.actor bound originInputs ∧
    (tracked bound target).content = original ∧ (tracked bound target).residual = target.snapshot bound := ⟨rfl, rfl, rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
