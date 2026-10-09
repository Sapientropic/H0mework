import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Dictionary
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Source

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame.Source
noncomputable section
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RawAction
  | old (action : CPS1Following.Source.RawAction)
  | adopt
  | pulse (time : ℝ)
  | deposit (amount : ℝ)

inductive Carrier (frame : CPS1Recycling.Frame)
  | following (old : CPS1Following.Source.Carrier frame)
  | molecular (state : Material frame)

def heldCarrier (frame : CPS1Recycling.Frame) (stock : Stock frame) : Option (Carrier frame) :=
  List.rec none (fun species _ tail => match species with
    | .retained (.retained (.retained (.retained (.joint joint)))) => some (.following (.reference (.joint joint)))
    | .retained (.retained (.retained (.quantum state))) => some (.following (.reference (.quantum state)))
    | .retained (.following state) => some (.following (.following state))
    | .molecular state => some (.molecular state)
    | _ => tail) stock

def RawAction.material (frame : CPS1Recycling.Frame) : RawAction → Stock frame
  | .old action => (action.material frame).map Species.retained
  | .adopt => []
  | .pulse time => [.retained (.retained (.retained (.rawTime time)))]
  | .deposit amount => [.retained (.retained (.retained (.rawEnergy amount)))]

def RawAction.reaction (frame : CPS1Recycling.Frame) (carrier : Option (Carrier frame)) : RawAction → Reaction frame
  | .old action => match carrier with
      | some (.following priorCarrier) => .retained (action.reaction frame (some priorCarrier))
      | _ => .requireCarrier
  | .adopt => match carrier with
      | some (.following (.following reference)) => .adopt reference
      | some (.molecular state) => .keepMolecular state
      | _ => .requireCarrier
  | .pulse time => match carrier with
      | some (.molecular state) => .pulse state time
      | _ => .requireCarrier
  | .deposit amount => match carrier with
      | some (.molecular state) => .deposit state amount
      | some (.following priorCarrier) => .retained ((CPS1Following.Source.RawAction.deposit amount).reaction frame (some priorCarrier))
      | _ => .requireCarrier

def RawAction.next (frame : CPS1Recycling.Frame) (carrier : Option (Carrier frame)) : RawAction → Option (Carrier frame)
  | .old action => match carrier with
      | some (.following priorCarrier) => (action.next frame (some priorCarrier)).map Carrier.following
      | _ => carrier
  | .adopt => match carrier with
      | some (.following (.following reference)) => match adopt? reference with
          | .ok next => some (.molecular next)
          | .error _ => carrier
      | _ => carrier
  | .pulse time => match carrier with
      | some (.molecular state) => match state.pulse? time with
          | .ok next => some (.molecular next)
          | .error _ => carrier
      | _ => carrier
  | .deposit amount => match carrier with
      | some (.molecular state) => match state.deposit? amount with
          | .ok next => some (.molecular next)
          | .error _ => carrier
      | some (.following priorCarrier) =>
          ((CPS1Following.Source.RawAction.deposit amount).next frame (some priorCarrier)).map Carrier.following
      | _ => carrier

def program (frame : CPS1Recycling.Frame) (carrier : Option (Carrier frame)) (actions : List RawAction) :
    List (Reaction frame) :=
  List.rec (motive := fun _ => Option (Carrier frame) → List (Reaction frame)) (fun _ => [])
    (fun action _ recur current => action.reaction frame current :: recur (action.next frame current)) actions carrier

structure Cursor (frame : CPS1Recycling.Frame) where
  stock : Stock frame
  pending : List RawAction
  stages : List (Execution frame)
  cut : Option (Species frame)

structure Occurrence (frame : CPS1Recycling.Frame) where
  previous : CPS1Following.Source.Occurrence frame
  current : Cursor frame

def fromActual (frame : CPS1Recycling.Frame) (previous : CPS1Following.Source.Occurrence frame) : Occurrence frame :=
  ⟨previous,⟨previous.current.stock.map Species.retained,previous.current.pending.map RawAction.old ++ [.adopt],[],none⟩⟩

def advance (frame : CPS1Recycling.Frame) (cursor : Cursor frame) (actions : List RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) : Cursor frame :=
  let available := cursor.stock ++
    feed.map (fun kind => Species.retained (.retained (.retained (.retained
      (CPS1EnzymeBath.componentSpecies frame kind))))) ++ actions.flatMap (RawAction.material frame)
  let requested := actions ++ cursor.pending
  let result := execute frame (program frame (heldCarrier frame available) requested) available
  ⟨result.stock,requested.drop result.fired.length,cursor.stages ++ [result],result.missing⟩

def execution (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1Following.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
    oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed
  let current := fromActual previous.1 previous.2
  pure ⟨previous.1,{current with current := advance previous.1 current.current actions feed}⟩

def resume (frame : CPS1Recycling.Frame) (current : Occurrence frame) (actions : List RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) : Occurrence frame :=
  {current with current := advance frame current.current actions feed}

theorem source_preserved (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (actions : List RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    (resume frame current actions feed).previous = current.previous := rfl

end
end CPS1MolecularFrame.Source
