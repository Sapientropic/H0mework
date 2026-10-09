import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath.Source
noncomputable section
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RawAction
  | attach (kind : Primary.TemplateKind)
  | report (address : CPS1AtomicDynamics.Charged.Address) (row : CPS1AtomicDynamics.Body.Row)
  | deposit (amount : ℝ)
  | pulse (dt : ℝ)
  deriving DecidableEq

/-- A bath feed is a fixed named raw molecule, not a complex, atom graph or pose. -/
def rawComponent (frame : CPS1Recycling.Frame) (kind : Primary.TemplateKind) : Species frame :=
  componentSpecies frame kind

def RawAction.material (frame : CPS1Recycling.Frame) : RawAction → Stock frame
  | .attach _ => []
  | .report address row => [.rawRow address row]
  | .deposit amount => [.rawEnergy amount]
  | .pulse dt => [.rawTime dt]

def RawAction.reaction (frame : CPS1Recycling.Frame) (state : Joint.State frame) : RawAction → Reaction frame
  | .attach kind => .attach state kind
  | .report address row => .report state address row
  | .deposit amount => .deposit state amount
  | .pulse dt => .pulse state dt

def RawAction.next (frame : CPS1Recycling.Frame) (state : Joint.State frame) : RawAction → Joint.State frame
  | .attach kind => Joint.attach frame state kind
  | .report address row => (Joint.report? frame state address row).toOption.getD state
  | .deposit amount => (Joint.deposit? frame state amount).toOption.getD state
  | .pulse dt => ((Joint.pulse? frame state dt).toOption.map Prod.fst).getD state

def program (frame : CPS1Recycling.Frame) (state : Joint.State frame) (actions : List RawAction) : List (Reaction frame) :=
  List.rec (motive := fun _ => Joint.State frame → List (Reaction frame)) (fun _ => [])
    (fun action _ recur current => action.reaction frame current :: recur (action.next frame current)) actions state

def heldJoint (frame : CPS1Recycling.Frame) (stock : Stock frame) : Option (Joint.State frame) :=
  List.rec none (fun species _ tail => match species with | .joint state => some state | _ => tail) stock

def liftBodyAction : CPS1AtomicDynamics.Source.RawAction → RawAction
  | .report address row => .report address row
  | .deposit amount => .deposit amount
  | .pulse dt => .pulse dt

def liftMaterial (frame : CPS1Recycling.Frame) : CPS1AtomicDynamics.Species frame → Species frame
  | .rawRow address row => .rawRow address row
  | .rawEnergy amount => .rawEnergy amount
  | .rawTime dt => .rawTime dt
  | other => .retained other

structure Cursor (frame : CPS1Recycling.Frame) where
  stock : Stock frame
  captureRemaining : List (Reaction frame)
  pending : List RawAction
  stages : List (Execution frame)
  cut : Option (Species frame)

def start (frame : CPS1Recycling.Frame) (previous : CPS1AtomicDynamics.Source.Occurrence frame) : Cursor frame :=
  let requested := match CPS1AtomicDynamics.Source.heldBody frame previous.current.stock with
    | some body => [.capture body] | none => [.requireBody]
  let result := execute frame requested (previous.current.stock.map (liftMaterial frame))
  ⟨result.stock,result.remaining,previous.current.pending.map liftBodyAction,[result],result.missing⟩

def advance (frame : CPS1Recycling.Frame) (cursor : Cursor frame)
    (actions : List RawAction) (feed : List Primary.TemplateKind) : Cursor frame :=
  let available := cursor.stock ++ feed.map (rawComponent frame) ++ actions.flatMap (RawAction.material frame)
  let requested := actions ++ cursor.pending
  let localProgram := match heldJoint frame available with | some state => program frame state requested | none => []
  let result := execute frame (cursor.captureRemaining ++ localProgram) available
  let paid := result.fired.length-cursor.captureRemaining.length
  ⟨result.stock,cursor.captureRemaining.drop result.fired.length,requested.drop paid,
    cursor.stages ++ [result],result.missing⟩

structure Occurrence (frame : CPS1Recycling.Frame) where
  previous : CPS1AtomicDynamics.Source.Occurrence frame
  current : Cursor frame

def fromActual (frame : CPS1Recycling.Frame) (previous : CPS1AtomicDynamics.Source.Occurrence frame) : Occurrence frame :=
  ⟨previous,start frame previous⟩

def execution (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (actions : List RawAction) (feed : List Primary.TemplateKind) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1AtomicDynamics.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth oldActions
  let current := fromActual previous.1 previous.2
  pure ⟨previous.1,{current with current := advance previous.1 current.current actions feed}⟩

def generatedPartnerProgram : List RawAction := [.attach .carbamoylPhosphate]

def generatedExecution (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (actions : List RawAction) (feed : List Primary.TemplateKind) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) :=
  execution edits water additional path recycleFeed scanFeed bodyFeed depth oldActions
    (generatedPartnerProgram ++ actions) feed

def resume (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (actions : List RawAction) (feed : List Primary.TemplateKind) : Occurrence frame :=
  {current with current := advance frame current.current actions feed}

theorem source_preserved (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (actions : List RawAction) (feed : List Primary.TemplateKind) :
    (resume frame current actions feed).previous = current.previous := rfl

end
end CPS1EnzymeBath.Source
