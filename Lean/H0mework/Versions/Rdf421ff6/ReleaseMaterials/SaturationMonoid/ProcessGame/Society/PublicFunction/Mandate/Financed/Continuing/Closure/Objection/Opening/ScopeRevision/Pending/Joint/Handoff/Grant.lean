import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Mandate.Lifecycle
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Handoff.Ready bound inputs)
noncomputable section

abbrev V := Lifecycle.vocabulary (Party := Bool) (Port := Mandate.Source.Port)
def wordAt (ordinal : Nat) := ProgrammeSource.rawEvent (I fresh) (ProgrammeHistory.visitAt (I fresh) ordinal).current
abbrev Item (ordinal : Nat) := {item // item ∈ (law fresh).rawItems (current fresh ordinal) (wordAt fresh ordinal)}

structure Refusal (ordinal : Nat) where
  private mk ::
  item : Item fresh ordinal
  operator : Bool
  target : State Bool Unit
  command : Command Bool
  operation : item.val.request.operation = .revise operator target
  marked : target.last = some command
  authentic : Observed.Authentic fresh.scope item.val.before item.val.request operator target command
  refused : ¬ (law fresh).Valid item.val.before item.val.request
  boundary : IsBoundary command

inductive Receipt where
  | private paid (ordinal : Nat) (actual : ActualCommand base fresh.scope (current fresh ordinal) (wordAt fresh ordinal))
      (boundary : IsBoundary actual.command)
  | private refused (ordinal : Nat) (actual : Refusal fresh ordinal)

def Receipt.ordinal : Receipt fresh → Nat
  | .paid ordinal .. | .refused ordinal .. => ordinal

def Receipt.command : Receipt fresh → Command Bool
  | .paid _ actual _ => actual.command
  | .refused _ actual => actual.command

def Receipt.item (receipt : Receipt fresh) : Item fresh (receipt.ordinal fresh) :=
  match receipt with
  | .paid _ actual _ => actual.item
  | .refused _ actual => actual.item

theorem Receipt.is_in_its_own_actual_execution (receipt : Receipt fresh) :
    (receipt.item fresh).val ∈ (I fresh).law.rawItems (current fresh (receipt.ordinal fresh))
      (wordAt fresh (receipt.ordinal fresh)) := (receipt.item fresh).property

def read (ordinal : Nat) (item : Item fresh ordinal) : Option (Receipt fresh) :=
  match recognize base fresh.scope (current fresh ordinal) (wordAt fresh ordinal) item with
  | some actual => if boundary : IsBoundary actual.command then some (.paid ordinal actual boundary) else none
  | none => match operation : item.val.request.operation with
    | .revise operator target => match marked : target.last with
      | none => none
      | some command =>
          if refused : ¬ (law fresh).Valid item.val.before item.val.request then
            if boundary : IsBoundary command then
              if authentic : Observed.Authentic fresh.scope item.val.before item.val.request operator target command then
                some (.refused ordinal ⟨item,operator,target,command,operation,marked,authentic,refused,boundary⟩)
              else none
            else none
          else none
    | _ => none

def receiptsAt (ordinal : Nat) : List (Receipt fresh) :=
  ((law fresh).rawItems (current fresh ordinal) (wordAt fresh ordinal)).attach.filterMap (read fresh ordinal)

def receipts (start count : Nat) := ((List.range count).map (fun offset => start + offset)).flatMap (receiptsAt fresh)

def Receipt.kind : Receipt fresh → LifecycleKind
  | .paid .. => .maintained
  | .refused .. => .deferred

-- A new jurisdiction cannot regrant or discharge the old mandate. Its actual
-- command records maintenance/refusal of the carried responsibility instead.
def Receipt.disposition (obligation : AdmittedObligation V) (receipt : Receipt fresh) :
    BoundaryDisposition V obligation obligation.admission.sourceEvent :=
  match receipt with
  | .paid .. => .carry (.maintained .generated)
  | .refused .. => .carry (.deferred .generated)

theorem Receipt.target_is_the_original_live_obligation (obligation : AdmittedObligation V) (receipt : Receipt fresh) :
    (receipt.disposition fresh obligation).targetSlot = .live obligation := by cases receipt <;> rfl

def Receipt.image (obligation : AdmittedObligation V) : Receipt fresh → LifecycleEvent V
  | .paid .. => .carried 0 obligation obligation.admission.sourceEvent (.maintained .generated)
  | .refused .. => .carried 0 obligation obligation.admission.sourceEvent (.deferred .generated)

variable (prior : NativeResponsibilityProcess V)

inductive Boundary (obligation : AdmittedObligation V) where
  | inherited (event : prior.BoundaryEvent obligation)
  | actual (receipt : Receipt fresh)

def process : NativeResponsibilityProcess V where
  AdmissionEvent := prior.AdmissionEvent
  admissionPayload := prior.admissionPayload
  BoundaryEvent := Boundary fresh prior
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
    | .actual receipt => receipt.disposition fresh _
  ReopenEvent := prior.ReopenEvent
  reopenPayload := prior.reopenPayload

def inheritRun {source target : ResponsibilityState V} : prior.Run source target → (process fresh prior).Run source target
  | .nil => .nil
  | .step path (.admit event) => .step (inheritRun path) (.admit event)
  | .step path (.cross slot obligation present event) => .step (inheritRun path) (.cross slot obligation present (.inherited event))
  | .step path (.reopen slot archive present event) => .step (inheritRun path) (.reopen slot archive present event)

theorem inheritRun_events {source target : ResponsibilityState V} (path : prior.Run source target) :
    (inheritRun fresh prior path).events = path.events := by
  induction path with
  | nil => rfl
  | step path edge ih => cases edge <;> simp only [inheritRun, NativeResponsibilityProcess.Run.events, ih] <;> rfl

structure Thread (origin : ResponsibilityState V) (obligation : AdmittedObligation V) where
  private mk ::
  state : ResponsibilityState V
  slots : state.slots = [.live obligation]
  crossing : (process fresh prior).Run origin state

variable {fresh prior}

def Thread.begin (state : ResponsibilityState V) (obligation : AdmittedObligation V)
    (slots : state.slots = [.live obligation]) : Thread fresh prior state obligation := ⟨state,slots,.nil⟩

def Thread.slot {origin : ResponsibilityState V} {obligation : AdmittedObligation V}
    (thread : Thread fresh prior origin obligation) : Fin thread.state.slots.length :=
  ⟨0, by rw [thread.slots]; exact Nat.zero_lt_succ 0⟩

def Thread.edge {origin : ResponsibilityState V} {obligation : AdmittedObligation V}
    (thread : Thread fresh prior origin obligation) (receipt : Receipt fresh) : (process fresh prior).Edge thread.state :=
  .cross thread.slot obligation (by simp [Thread.slot, thread.slots]) (.actual receipt)

def Thread.step {origin : ResponsibilityState V} {obligation : AdmittedObligation V}
    (thread : Thread fresh prior origin obligation) (receipt : Receipt fresh) : Thread fresh prior origin obligation :=
  ⟨(thread.edge receipt).target, by
    change thread.state.slots.set thread.slot (receipt.disposition fresh obligation).targetSlot = _
    rw [receipt.target_is_the_original_live_obligation]
    simp [Thread.slot,thread.slots], .step thread.crossing (thread.edge receipt)⟩

def Thread.consume {origin : ResponsibilityState V} {obligation : AdmittedObligation V}
    (thread : Thread fresh prior origin obligation) (receipts : List (Receipt fresh)) : Thread fresh prior origin obligation :=
  receipts.foldl Thread.step thread

theorem Thread.step_history {origin : ResponsibilityState V} {obligation : AdmittedObligation V}
    (thread : Thread fresh prior origin obligation) (receipt : Receipt fresh) :
    (thread.step receipt).state.history = thread.state.history ++ [receipt.image fresh obligation] := by
  cases receipt <;> rfl

theorem Thread.consume_history {origin : ResponsibilityState V} {obligation : AdmittedObligation V}
    (thread : Thread fresh prior origin obligation) (actual : List (Receipt fresh)) :
    (thread.consume actual).state.history = thread.state.history ++ actual.map (Receipt.image fresh obligation) := by
  induction actual generalizing thread with
  | nil => exact (List.append_nil _).symm
  | cons receipt rest ih =>
    change ((thread.step receipt).consume rest).state.history = _
    rw [ih,Thread.step_history]
    simp only [List.map_cons,List.append_assoc,List.singleton_append]

theorem actual_run_events (state : ResponsibilityState V) (obligation : AdmittedObligation V)
    (slots : state.slots = [.live obligation]) (actual : List (Receipt fresh)) :
    ((Thread.begin (fresh := fresh) (prior := prior) state obligation slots).consume actual).crossing.events =
      actual.map (Receipt.image fresh obligation) := by
  apply List.append_cancel_left (as := state.history)
  exact ((Thread.begin (fresh := fresh) (prior := prior) state obligation slots).consume actual).crossing.history_eq.symm.trans
    (Thread.consume_history _ actual)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant
