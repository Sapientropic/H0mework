import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Grant

/-! A saved Challenge keeps its original vocabulary, snapshot and generated
state while successive actual inputs extend its native process. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Challenge

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Mandate.Challenge
noncomputable section
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)}

def withSlots {originInputs : List (List Action)} {original : Mandate.Challenge.Claim (fromHistory bound) originInputs}
    {first last : ResponsibilityState (Mandate.Challenge.V (fromHistory bound) originInputs)}
    (shape : ScopeProcess.Shape (fromHistory bound) originInputs original first) (same : last.slots = first.slots) :
    ScopeProcess.Shape (fromHistory bound) originInputs original last := by
  cases shape with
  | pending obligation slots content jurisdiction anchor => exact .pending obligation (same.trans slots) content jurisdiction anchor
  | closed archive slots => exact .closed archive (same.trans slots)

inductive Code where
  | seed
  | step (past : Code) (source : ScopeBoundary.Source base)
      (later : oldScope.task.deadline < source.scope.task.earliest)

def processAt (fresh : Handoff.Ready bound inputs) (record : Cross.Resident bound inputs) : Code (oldScope := oldScope) →
    NativeResponsibilityProcess (Mandate.Challenge.V (fromHistory bound) record.originInputs)
  | .seed => ScopeProcess.process (fromHistory bound) record.originInputs (Handoff.Challenge.occurrence fresh)
      (Handoff.Challenge.laterWindow fresh) (Handoff.Challenge.prior record) record.original
  | .step past source later => ScopeProcess.process (fromHistory bound) record.originInputs source later (processAt fresh record past) record.original

structure Saved (fresh : Handoff.Ready bound inputs) (record : Cross.Resident bound inputs) where
  private mk ::
  code : Code (oldScope := oldScope)
  state : (processAt fresh record code).GeneratedState
  shape : ScopeProcess.Shape (fromHistory bound) record.originInputs record.original state.current

variable {fresh : Handoff.Ready bound inputs}
def Saved.native {record : Cross.Resident bound inputs} (saved : Saved fresh record) := processAt fresh record saved.code

def beginAt {count : Nat} (entry : Handoff.Challenge.Entry fresh count) : Saved fresh entry.original :=
  ⟨.seed,entry.continuation.state,withSlots (Handoff.Challenge.shape entry.original) entry.continuation.slots⟩

def initial (entry : Handoff.Challenge.Entry fresh 4) : Saved fresh entry.original :=
  ⟨.seed,entry.continuation.state,withSlots (Handoff.Challenge.shape entry.original) entry.continuation.slots⟩

def Saved.thread {record : Cross.Resident bound inputs} (saved : Saved fresh record)
    (source : ScopeBoundary.Source base) (later : oldScope.task.deadline < source.scope.task.earliest)
    (receipts : List (ScopeBoundary.Receipt source)) :=
  (ScopeProcess.begin (fromHistory bound) record.originInputs source later (original := record.original) saved.state).consume
    (fromHistory bound) record.originInputs source later saved.shape receipts

def Saved.consume {record : Cross.Resident bound inputs} (saved : Saved fresh record)
    (source : ScopeBoundary.Source base) (later : oldScope.task.deadline < source.scope.task.earliest)
    (receipts : List (ScopeBoundary.Receipt source)) : Saved fresh record :=
  ⟨.step saved.code source later,
    (saved.thread source later receipts).state,withSlots saved.shape (saved.thread source later receipts).slots⟩

def images {record : Cross.Resident bound inputs} (saved : Saved fresh record)
    (source : ScopeBoundary.Source base) (later : oldScope.task.deadline < source.scope.task.earliest)
    (receipts : List (ScopeBoundary.Receipt source)) : List (LifecycleEvent (Mandate.Challenge.V (fromHistory bound) record.originInputs)) :=
  match saved.shape with
  | .pending obligation _ content jurisdiction _ => receipts.map (ScopeProcess.image (fromHistory bound) record.originInputs source later obligation content jurisdiction)
  | .closed .. => []

theorem Saved.consume_history {record : Cross.Resident bound inputs} (saved : Saved fresh record)
    (source : ScopeBoundary.Source base) (later : oldScope.task.deadline < source.scope.task.earliest)
    (receipts : List (ScopeBoundary.Receipt source)) :
    (saved.consume source later receipts).state.current.history = saved.state.current.history ++ images saved source later receipts := by
  rcases saved with ⟨native,state,shape⟩
  cases shape with
  | pending obligation slots content jurisdiction anchor =>
    exact ScopeProcess.Thread.consume_history _ _ _ _ _ slots content jurisdiction anchor _ receipts
  | closed archive slots =>
    change ((ScopeProcess.begin _ _ source later (original := record.original) state).consume _ _ _ _ (.closed archive slots) receipts).state.current.history = state.current.history ++ []
    rw [ScopeProcess.Thread.closed_is_literal]
    exact (List.append_nil _).symm

theorem Saved.consume_slots {record : Cross.Resident bound inputs} (saved : Saved fresh record)
    (source : ScopeBoundary.Source base) (later : oldScope.task.deadline < source.scope.task.earliest)
    (receipts : List (ScopeBoundary.Receipt source)) :
    (saved.consume source later receipts).state.current.slots = saved.state.current.slots := (saved.thread source later receipts).slots

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Challenge
