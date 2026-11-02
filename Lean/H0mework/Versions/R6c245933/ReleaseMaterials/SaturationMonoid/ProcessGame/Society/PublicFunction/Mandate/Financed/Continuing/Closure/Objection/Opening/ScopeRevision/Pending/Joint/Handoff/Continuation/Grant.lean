import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Epoch

/-! Saved grants retain their original admission and complete native run.
Each later input extends that process with receipts decoded by its own law. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Mandate.Lifecycle
noncomputable section

namespace Grant
abbrev V := Handoff.Grant.V
variable (source : Mandate.Challenge.ScopeBoundary.Source base) (prior : NativeResponsibilityProcess V)

inductive Boundary (obligation : AdmittedObligation V) where
  | inherited (event : prior.BoundaryEvent obligation)
  | actual (receipt : Mandate.Challenge.ScopeBoundary.Receipt source)

def carry (receipt : Mandate.Challenge.ScopeBoundary.Receipt source) (obligation : AdmittedObligation V) :
    ActiveCarryDisposition V obligation obligation.admission.sourceEvent :=
  if receipt.accepted source then .maintained .generated else .deferred .generated

def process : NativeResponsibilityProcess V where
  AdmissionEvent := prior.AdmissionEvent
  admissionPayload := prior.admissionPayload
  BoundaryEvent := Boundary source prior
  boundarySource := fun {obligation} event => match event with
    | .inherited event => prior.boundarySource event
    | .actual _ => obligation.admission.sourceEvent
  boundary_anchor_eq := fun event => by cases event with
    | inherited event => exact prior.boundary_anchor_eq event
    | actual _ => rfl
  boundary_incidence_eq := fun event => by cases event with
    | inherited event => exact prior.boundary_incidence_eq event
    | actual _ => rfl
  boundaryDisposition := fun event => match event with
    | .inherited event => prior.boundaryDisposition event
    | .actual receipt => .carry (carry source receipt _)
  ReopenEvent := prior.ReopenEvent
  reopenPayload := prior.reopenPayload

def inheritRun {first last : ResponsibilityState V} : prior.Run first last → (process source prior).Run first last
  | .nil => .nil
  | .step path (.admit event) => .step (inheritRun path) (.admit event)
  | .step path (.cross slot obligation present event) => .step (inheritRun path) (.cross slot obligation present (.inherited event))
  | .step path (.reopen slot archive present event) => .step (inheritRun path) (.reopen slot archive present event)

theorem inheritRun_events {first last : ResponsibilityState V} (path : prior.Run first last) :
    (inheritRun source prior path).events = path.events := by
  induction path with
  | nil => rfl
  | step path edge ih => cases edge <;> simp only [inheritRun, NativeResponsibilityProcess.Run.events, ih] <;> rfl

variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)}

abbrev origin (record : Mandate.Challenge.Cross.GrantResident bound inputs) :=
  Observed.initialState base oldScope (Mandate.Challenge.Cross.grantCurrent bound inputs)
    (Mandate.Challenge.Cross.grantWord bound inputs) record.birth.val record.grant

inductive Code where
  | seed
  | step (past : Code) (source : Mandate.Challenge.ScopeBoundary.Source base)
      (receipt : Mandate.Challenge.ScopeBoundary.Receipt source)

def processAt (fresh : Handoff.Ready bound inputs) (record : Mandate.Challenge.Cross.GrantResident bound inputs) : Code → NativeResponsibilityProcess V
  | .seed => Handoff.Grant.process fresh (Handoff.Grant.prior record)
  | .step past source _ => process source (processAt fresh record past)

structure Saved (fresh : Handoff.Ready bound inputs) (record : Mandate.Challenge.Cross.GrantResident bound inputs) where
  private mk ::
  code : Code
  state : ResponsibilityState V
  slots : state.slots = [.live record.history.obligation]
  entire : (processAt fresh record code).Run (origin record) state

variable {fresh : Handoff.Ready bound inputs}
def Saved.native {record : Mandate.Challenge.Cross.GrantResident bound inputs} (saved : Saved fresh record) := processAt fresh record saved.code

def beginAt {count : Nat} (entry : Handoff.Grant.Entry fresh count) : Saved fresh entry.original :=
  ⟨.seed,entry.continuation.state,entry.continuation.slots,entry.entire⟩

def initial (entry : Handoff.Grant.Entry fresh 4) : Saved fresh entry.original :=
  ⟨.seed,entry.continuation.state,entry.continuation.slots,entry.entire⟩

variable {source prior}
def Saved.step {record : Mandate.Challenge.Cross.GrantResident bound inputs} (saved : Saved fresh record)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (receipt : Mandate.Challenge.ScopeBoundary.Receipt source) : Saved fresh record := by
  let address : Fin saved.state.slots.length := ⟨0,by rw [saved.slots]; exact Nat.zero_lt_succ 0⟩
  let edge : (process source saved.native).Edge saved.state :=
    .cross address record.history.obligation (by simp [address,saved.slots]) (.actual receipt)
  refine ⟨.step saved.code source receipt,edge.target,?_,.step (inheritRun source saved.native saved.entire) edge⟩
  change saved.state.slots.set address (.live _) = _
  simp only [saved.slots,address,List.set_cons_zero]
  unfold carry
  split <;> rfl

def image (source : Mandate.Challenge.ScopeBoundary.Source base) (obligation : AdmittedObligation V)
    (receipt : Mandate.Challenge.ScopeBoundary.Receipt source) : LifecycleEvent V :=
  .carried 0 obligation obligation.admission.sourceEvent (carry source receipt obligation)

theorem Saved.step_history {record : Mandate.Challenge.Cross.GrantResident bound inputs} (saved : Saved fresh record)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (receipt : Mandate.Challenge.ScopeBoundary.Receipt source) :
    (saved.step source receipt).state.history = saved.state.history ++ [image source record.history.obligation receipt] := rfl

def Saved.consume {record : Mandate.Challenge.Cross.GrantResident bound inputs} (saved : Saved fresh record)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) : Saved fresh record :=
  receipts.foldl (fun current receipt => current.step source receipt) saved

theorem Saved.consume_history {record : Mandate.Challenge.Cross.GrantResident bound inputs} (saved : Saved fresh record)
    (source : Mandate.Challenge.ScopeBoundary.Source base) (receipts : List (Mandate.Challenge.ScopeBoundary.Receipt source)) :
    (saved.consume source receipts).state.history = saved.state.history ++ receipts.map (image source record.history.obligation) := by
  induction receipts generalizing saved with
  | nil => exact (List.append_nil _).symm
  | cons receipt rest ih =>
    change ((saved.step source receipt).consume source rest).state.history = _
    rw [ih,Saved.step_history]
    simp only [List.map_cons,List.append_assoc,List.singleton_append]

end Grant
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation
