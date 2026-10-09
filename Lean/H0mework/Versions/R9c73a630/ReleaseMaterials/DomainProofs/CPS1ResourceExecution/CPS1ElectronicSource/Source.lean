import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource.Source
noncomputable section
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RawAction
  | old (action : CPS1EnzymeBath.Source.RawAction)
  | prepare
  | electronicDeposit (amount : ℝ)
  | electronicPulse (time : ℝ)

def liftMaterial (frame : CPS1Recycling.Frame) : CPS1EnzymeBath.Species frame → Species frame
  | .rawRow address row => .rawRow address row
  | .rawEnergy amount => .rawEnergy amount
  | .rawTime time => .rawTime time
  | other => .retained other

def RawAction.material (frame : CPS1Recycling.Frame) : RawAction → Stock frame
  | .old action => (action.material frame).map (liftMaterial frame)
  | .prepare => []
  | .electronicDeposit amount => [.rawEnergy amount]
  | .electronicPulse time => [.rawTime time]

def heldCarrier (frame : CPS1Recycling.Frame) (stock : Stock frame) : Option (Carrier frame) :=
  List.rec none (fun species _ tail => match species with
    | .retained (.joint joint) => some (.joint joint)
    | .quantum state => some (.quantum state)
    | _ => tail) stock

def RawAction.reaction (frame : CPS1Recycling.Frame) (carrier : Option (Carrier frame)) :
    RawAction → Reaction frame
  | .old action => match carrier with
    | some (.joint joint) => match action with
      | .attach kind => .jointAttach joint kind
      | .report address row => .jointReport joint address row
      | .deposit amount => .jointDeposit joint amount
      | .pulse time => .jointPulse joint time
    | _ => .requireCarrier
  | .prepare => match carrier with
    | some (.joint joint) => .prepare joint
    | some (.quantum state) => .keepQuantum state
    | none => .requireCarrier
  | .electronicDeposit amount => match carrier with
    | some (.joint joint) => .jointDeposit joint amount
    | some (.quantum state) => .quantumDeposit state amount
    | none => .requireCarrier
  | .electronicPulse time => match carrier with
    | some (.quantum state) => .quantumPulse state time
    | _ => .requireCarrier

def RawAction.next (frame : CPS1Recycling.Frame) (carrier : Option (Carrier frame)) :
    RawAction → Option (Carrier frame)
  | .old action => match carrier with
    | some (.joint joint) => some (.joint (action.next frame joint))
    | _ => carrier
  | .prepare => match carrier with
    | some (.joint joint) => match State.fromJoint? frame joint with
      | .ok state => some (.quantum state)
      | .error _ => carrier
    | _ => carrier
  | .electronicDeposit amount => match carrier with
    | some (.joint joint) => match CPS1EnzymeBath.Joint.deposit? frame joint amount with
      | .ok next => some (.joint next)
      | .error _ => carrier
    | some (.quantum state) => match state.deposit? amount with
      | .ok next => some (.quantum next)
      | .error _ => carrier
    | none => none
  | .electronicPulse time => match carrier with
    | some (.quantum state) => match state.pulse? time with
      | .ok next => some (.quantum next)
      | .error _ => carrier
    | _ => carrier

def program (frame : CPS1Recycling.Frame) (carrier : Option (Carrier frame))
    (actions : List RawAction) : List (Reaction frame) :=
  List.rec (motive := fun _ => Option (Carrier frame) → List (Reaction frame)) (fun _ => [])
    (fun action _ recur current => action.reaction frame current ::
      recur (action.next frame current)) actions carrier

structure Cursor (frame : CPS1Recycling.Frame) where
  stock : Stock frame
  pending : List RawAction
  stages : List (Execution frame)
  cut : Option (Species frame)

def start (frame : CPS1Recycling.Frame) (previous : CPS1EnzymeBath.Source.Occurrence frame) : Cursor frame :=
  let stock := previous.current.stock.map (liftMaterial frame)
  let requested := previous.current.pending.map RawAction.old ++ [.prepare]
  let result := execute frame (program frame (heldCarrier frame stock) requested) stock
  ⟨result.stock,requested.drop result.fired.length,[result],result.missing⟩

def advance (frame : CPS1Recycling.Frame) (cursor : Cursor frame) (actions : List RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) : Cursor frame :=
  let available := cursor.stock ++
    feed.map (fun kind => Species.retained (CPS1EnzymeBath.componentSpecies frame kind)) ++
    actions.flatMap (RawAction.material frame)
  let requested := actions ++ cursor.pending
  let result := execute frame (program frame (heldCarrier frame available) requested) available
  ⟨result.stock,requested.drop result.fired.length,cursor.stages ++ [result],result.missing⟩

structure Occurrence (frame : CPS1Recycling.Frame) where
  previous : CPS1EnzymeBath.Source.Occurrence frame
  current : Cursor frame

def fromActual (frame : CPS1Recycling.Frame) (previous : CPS1EnzymeBath.Source.Occurrence frame) : Occurrence frame :=
  ⟨previous,start frame previous⟩

def execution (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1EnzymeBath.Source.generatedExecution edits water additional path
    recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
  let current := fromActual previous.1 previous.2
  pure ⟨previous.1,{current with current := advance previous.1 current.current actions feed}⟩

def resume (frame : CPS1Recycling.Frame) (current : Occurrence frame) (actions : List RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) : Occurrence frame :=
  {current with current := advance frame current.current actions feed}

theorem source_preserved (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (actions : List RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    (resume frame current actions feed).previous = current.previous := rfl

end
end CPS1ElectronicSource.Source
