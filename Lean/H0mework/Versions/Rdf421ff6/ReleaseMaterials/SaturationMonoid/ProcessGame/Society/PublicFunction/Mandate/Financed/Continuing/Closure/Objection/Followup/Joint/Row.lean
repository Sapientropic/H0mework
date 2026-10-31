import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Continuation

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

abbrev Origin (fuel : ℚ) := (inputs : List (List Action)) × Claim fuel inputs

variable {fuel : ℚ} {inputs : List (List Action)}

abbrev Event (cut : Cut fuel inputs) := {position : Position fuel inputs // position.ordinal < cut.depth + 2}

structure Thread (origin : Origin fuel) (cut : Cut fuel inputs) where
  private mk ::
  history : Cross.History origin.2 inputs
  within : history.Within (cut.depth + 2)

abbrev Row (cut : Cut fuel inputs) := (origin : Origin fuel) × Thread origin cut

def seed (cut : Cut fuel inputs) (claim : Claim fuel inputs) (inside : claim.position.ordinal < cut.depth + 2) : Row cut :=
  ⟨⟨inputs, claim⟩, ⟨Cross.History.inherit (Followup.through fuel inputs claim (cut.depth + 2)),
    Cross.inherit_within _ _ (Cross.local_through_within _ _ _ inside (Nat.le_refl _))⟩⟩

/-- Admission occurs at this actual signature. Later items of the same word
are consumed by the joint fold, rather than read ahead by this factory. -/
def birth (cut : Cut fuel inputs) (claim : Claim fuel inputs) (inside : claim.position.ordinal < cut.depth + 2) : Row cut :=
  ⟨⟨inputs, claim⟩, ⟨.pending (Cross.Target.local .initial)
    ((NativeResponsibilityProcess.GeneratedState.initial (Cross.process claim)).step (Cross.process claim) (.admit ())) rfl,
      inside⟩⟩

def Thread.receive {origin : Origin fuel} {cut : Cut fuel inputs} (thread : Thread origin cut) (event : Event cut) : Thread origin cut :=
  ⟨thread.history.receive event.val, Cross.receive_within _ _ _ thread.within event.property⟩

def Thread.receiveRun {origin : Origin fuel} {cut : Cut fuel inputs} (thread : Thread origin cut) (event : Event cut) :
    (Cross.process origin.2).Run thread.history.state.current (thread.receive event).history.state.current :=
  Cross.receiveRun thread.history event.val

def Thread.fold {origin : Origin fuel} {cut : Cut fuel inputs} (thread : Thread origin cut) : List (Event cut) → Thread origin cut
  | [] => thread
  | event :: tail => (thread.receive event).fold tail

def Thread.foldRun {origin : Origin fuel} {cut : Cut fuel inputs} (thread : Thread origin cut) : (events : List (Event cut)) →
    (Cross.process origin.2).Run thread.history.state.current (thread.fold events).history.state.current
  | [] => .nil
  | event :: tail => (thread.receiveRun event).concatRuns _ ((thread.receive event).foldRun tail)

def Thread.transport {origin : Origin fuel} {cut : Cut fuel inputs} (thread : Thread origin cut) (word : List Action) :
    Thread origin (afterInput cut word) :=
  ⟨Cross.transportHistory cut word thread.history thread.within,
    Cross.transported_within cut word thread.history thread.within⟩

theorem Thread.transport_state {origin : Origin fuel} {cut : Cut fuel inputs} (thread : Thread origin cut) (word : List Action) :
    (thread.transport word).history.state = thread.history.state :=
  Cross.transport_preserves_the_entire_generated_state cut word thread.history thread.within

def Row.receive {cut : Cut fuel inputs} (row : Row cut) (event : Event cut) : Row cut := ⟨row.1, row.2.receive event⟩

def Row.follow {cut : Cut fuel inputs} (row : Row cut) (events : List (Event cut)) : Row cut := ⟨row.1, row.2.fold events⟩

def Row.transport {cut : Cut fuel inputs} (row : Row cut) (word : List Action) : Row (afterInput cut word) :=
  ⟨row.1, row.2.transport word⟩

def Row.isPending {cut : Cut fuel inputs} (row : Row cut) := row.2.history.isPending

def Row.matches {cut : Cut fuel inputs} (row : Row cut) : Bool :=
  match row.2.history with
  | .closed .. => false
  | .pending target _ _ => decide (target.snapshot = cut.past.frame.raw.technology)

def Row.canReconfirm {cut : Cut fuel inputs} (row : Row cut) (event : Event cut) : Bool :=
  match row.2.history with
  | .closed .. => false
  | .pending target _ _ => (Cross.readReconfirmation target event.val).isSome

theorem birth_uses_original_native_admission (cut : Cut fuel inputs) (claim : Claim fuel inputs)
    (inside : claim.position.ordinal < cut.depth + 2) :
    (birth cut claim inside).2.history.state.current.slots = [.live (obligation fuel inputs claim)] ∧
    (birth cut claim inside).2.history.state.current.history.map LifecycleEvent.kind = [.admitted] := ⟨rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint
