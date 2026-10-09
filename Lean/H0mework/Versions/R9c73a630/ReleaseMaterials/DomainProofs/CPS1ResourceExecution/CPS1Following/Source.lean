import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following.Source
noncomputable section
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RawAction
  | old (action : CPS1QuantumNuclear.Source.RawAction)
  | relocate
  | pulse (time : ℝ)
  | deposit (amount : ℝ)

inductive Carrier (frame : CPS1Recycling.Frame)
  | reference (old : CPS1ElectronicSource.Carrier frame)
  | following (state : CPS1ElectronicSource.State frame)

def heldCarrier (frame : CPS1Recycling.Frame) (stock : Stock frame) : Option (Carrier frame) :=
  List.rec none (fun species _ tail => match species with
    | .retained (.retained (.retained (.joint joint))) => some (.reference (.joint joint))
    | .retained (.retained (.quantum state)) => some (.reference (.quantum state))
    | .following state => some (.following state)
    | _ => tail) stock

def RawAction.material (frame : CPS1Recycling.Frame) : RawAction → Stock frame
  | .old action => (action.material frame).map Species.retained
  | .relocate => []
  | .pulse time => [.retained (.retained (.rawTime time))]
  | .deposit amount => [.retained (.retained (.rawEnergy amount))]

def RawAction.reaction (frame : CPS1Recycling.Frame) (carrier : Option (Carrier frame)) : RawAction → Reaction frame
  | .old action => match carrier with
      | some (.reference current) => .retained (action.reaction frame (some current))
      | _ => .retained (.retained .requireCarrier)
  | .relocate => match carrier with
      | some (.reference (.quantum state)) => .relocate state
      | some (.following state) => .keepFollowing state
      | _ => .retained (.retained .requireCarrier)
  | .pulse time => match carrier with
      | some (.following state) => .pulse state time
      | _ => .retained (.retained .requireCarrier)
  | .deposit amount => match carrier with
      | some (.following state) => .deposit state amount
      | some (.reference (.quantum state)) => .retained (.retained (.quantumDeposit state amount))
      | some (.reference (.joint joint)) => .retained (.retained (.jointDeposit joint amount))
      | _ => .retained (.retained .requireCarrier)

def RawAction.next (frame : CPS1Recycling.Frame) (carrier : Option (Carrier frame)) : RawAction → Option (Carrier frame)
  | .old action => match carrier with
      | some (.reference current) => (action.next frame (some current)).map Carrier.reference
      | _ => carrier
  | .relocate => match carrier with
      | some (.reference (.quantum state)) => match relocate? state with
          | .ok next => some (.following next.1) | .error _ => carrier
      | _ => carrier
  | .pulse time => match carrier with
      | some (.following state) => match pulse? state time with
          | .ok next => some (.following next.1) | .error _ => carrier
      | _ => carrier
  | .deposit amount => match carrier with
      | some (.following state) => match deposit? state amount with
          | .ok next => some (.following next) | .error _ => carrier
      | some (.reference current) =>
          ((CPS1ElectronicSource.Source.RawAction.electronicDeposit amount).next frame (some current)).map Carrier.reference
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
  previous : CPS1QuantumNuclear.Source.Occurrence frame
  current : Cursor frame

def fromActual (frame : CPS1Recycling.Frame) (previous : CPS1QuantumNuclear.Source.Occurrence frame) : Occurrence frame :=
  ⟨previous,⟨previous.current.stock.map Species.retained,previous.current.pending.map RawAction.old,[],none⟩⟩

def advance (frame : CPS1Recycling.Frame) (cursor : Cursor frame) (actions : List RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) : Cursor frame :=
  let available := cursor.stock ++
    feed.map (fun kind => Species.retained (.retained (.retained (CPS1EnzymeBath.componentSpecies frame kind)))) ++
    actions.flatMap (RawAction.material frame)
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
    (actions : List RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1QuantumNuclear.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
    oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
  let current := fromActual previous.1 previous.2
  pure ⟨previous.1,{current with current := advance previous.1 current.current actions feed}⟩

def resume (frame : CPS1Recycling.Frame) (current : Occurrence frame) (actions : List RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) : Occurrence frame :=
  {current with current := advance frame current.current actions feed}

theorem source_preserved (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (actions : List RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    (resume frame current actions feed).previous = current.previous := rfl

end
end CPS1Following.Source
