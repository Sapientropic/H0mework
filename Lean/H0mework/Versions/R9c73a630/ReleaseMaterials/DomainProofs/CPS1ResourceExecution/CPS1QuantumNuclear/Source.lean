import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear.Source
noncomputable section
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RawAction
  | old (action : CPS1ElectronicSource.Source.RawAction)
  | nuclearPulse (time : ℝ)

def heldCarrier (frame : CPS1Recycling.Frame) (stock : Stock frame) :
    Option (CPS1ElectronicSource.Carrier frame) :=
  List.rec none (fun species _ tail => match species with
    | .retained (.retained (.joint joint)) => some (.joint joint)
    | .retained (.quantum state) => some (.quantum state)
    | _ => tail) stock

def RawAction.material (frame : CPS1Recycling.Frame) : RawAction → Stock frame
  | .old action => (action.material frame).map Species.retained
  | .nuclearPulse time => [.retained (.rawTime time)]

def RawAction.reaction (frame : CPS1Recycling.Frame)
    (carrier : Option (CPS1ElectronicSource.Carrier frame)) : RawAction → Reaction frame
  | .old action => .retained (action.reaction frame carrier)
  | .nuclearPulse time => match carrier with
    | some (.quantum state) => .nuclearPulse state time
    | _ => .retained .requireCarrier

def RawAction.next (frame : CPS1Recycling.Frame)
    (carrier : Option (CPS1ElectronicSource.Carrier frame)) : RawAction → Option (CPS1ElectronicSource.Carrier frame)
  | .old action => action.next frame carrier
  | .nuclearPulse time => match carrier with
    | some (.quantum state) => match pulse? state time with
      | .ok next => some (.quantum next.1)
      | .error _ => carrier
    | _ => carrier

def program (frame : CPS1Recycling.Frame) (carrier : Option (CPS1ElectronicSource.Carrier frame))
    (actions : List RawAction) : List (Reaction frame) :=
  List.rec (motive := fun _ => Option (CPS1ElectronicSource.Carrier frame) → List (Reaction frame)) (fun _ => [])
    (fun action _ recur current => action.reaction frame current :: recur (action.next frame current)) actions carrier

structure Cursor (frame : CPS1Recycling.Frame) where
  stock : Stock frame
  pending : List RawAction
  stages : List (Execution frame)
  cut : Option (Species frame)

structure Occurrence (frame : CPS1Recycling.Frame) where
  previous : CPS1ElectronicSource.Source.Occurrence frame
  current : Cursor frame

def fromActual (frame : CPS1Recycling.Frame) (previous : CPS1ElectronicSource.Source.Occurrence frame) : Occurrence frame :=
  ⟨previous,⟨previous.current.stock.map Species.retained,previous.current.pending.map RawAction.old,[],none⟩⟩

def advance (frame : CPS1Recycling.Frame) (cursor : Cursor frame) (actions : List RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) : Cursor frame :=
  let available := cursor.stock ++
    feed.map (fun kind => Species.retained (.retained (CPS1EnzymeBath.componentSpecies frame kind))) ++
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
    (actions : List RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1ElectronicSource.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
    oldActions bathActions bathFeed electronicActions electronicFeed
  let current := fromActual previous.1 previous.2
  pure ⟨previous.1,{current with current := advance previous.1 current.current actions feed}⟩

def resume (frame : CPS1Recycling.Frame) (current : Occurrence frame) (actions : List RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) : Occurrence frame :=
  {current with current := advance frame current.current actions feed}

theorem source_preserved (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (actions : List RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    (resume frame current actions feed).previous = current.previous := rfl

end
end CPS1QuantumNuclear.Source
