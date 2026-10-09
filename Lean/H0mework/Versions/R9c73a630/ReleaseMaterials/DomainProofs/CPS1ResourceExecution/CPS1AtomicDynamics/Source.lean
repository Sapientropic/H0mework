import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1AtomicDynamics.Source
noncomputable section
open CPS1ResourceExecution CPS1LocalChemicalExecution CPS1AtomicSource
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RawAction
  | report (address : Charged.Address) (row : Body.Row)
  | deposit (amount : ℝ)
  | pulse (dt : ℝ)
  deriving DecidableEq

def RawAction.material (frame : CPS1Recycling.Frame) : RawAction → Stock frame
  | .report address row => [.rawRow address row]
  | .deposit amount => [.rawEnergy amount]
  | .pulse dt => [.rawTime dt]

def RawAction.reaction (frame : CPS1Recycling.Frame) (state : Body.State frame) : RawAction → Reaction frame
  | .report address row => .report state address row
  | .deposit amount => .deposit state amount
  | .pulse dt => .pulse state dt

def RawAction.next (frame : CPS1Recycling.Frame) (state : Body.State frame) : RawAction → Body.State frame
  | .report address row => (Body.report? frame state address row).toOption.getD state
  | .deposit amount => (Body.deposit? frame state amount).toOption.getD state
  | .pulse dt => ((Body.pulse? frame state dt).toOption.map Prod.fst).getD state

def program (frame : CPS1Recycling.Frame) (state : Body.State frame) (actions : List RawAction) :
    List (Reaction frame) :=
  List.rec (motive := fun _ => Body.State frame → List (Reaction frame)) (fun _ => [])
    (fun action _ recur current => action.reaction frame current :: recur (action.next frame current)) actions state

def heldAtomic (frame : CPS1Recycling.Frame) (stock : Current.Stock frame) : Option (Chain frame) :=
  List.rec none (fun species _ tail => match species with | .atomic chain => some chain | _ => tail) stock

def heldBody (frame : CPS1Recycling.Frame) (stock : Stock frame) : Option (Body.State frame) :=
  List.rec none (fun species _ tail => match species with | .body state => some state | _ => tail) stock

structure Cursor (frame : CPS1Recycling.Frame) where
  stock : Stock frame
  captureRemaining : List (Reaction frame)
  pending : List RawAction
  stages : List (Execution frame)
  cut : Option (Species frame)

def start (frame : CPS1Recycling.Frame) (previous : Current.Occurrence frame) : Cursor frame :=
  let raw := previous.current.stock.map Species.retained
  let requested := match heldAtomic frame previous.current.stock with
    | some chain => [.capture chain] | none => [.requireAtomic]
  let result := execute frame requested raw
  ⟨result.stock,result.remaining,[],[result],result.missing⟩

/-- Reports/deposits may precede and pay an old failed pulse. Pending actions are
replanned from the actual body; their raw material is not injected a second time. -/
def advance (frame : CPS1Recycling.Frame) (cursor : Cursor frame) (actions : List RawAction) : Cursor frame :=
  let available := cursor.stock ++ actions.flatMap (RawAction.material frame)
  let requested := actions ++ cursor.pending
  let localProgram :=  match heldBody frame available with
    | some state => program frame state requested | none => []
  let result := execute frame (cursor.captureRemaining ++ localProgram) available
  let paid := result.fired.length - cursor.captureRemaining.length
  ⟨result.stock,cursor.captureRemaining.drop result.fired.length,requested.drop paid,
    cursor.stages ++ [result],result.missing⟩

structure Occurrence (frame : CPS1Recycling.Frame) where
  previous : Current.Occurrence frame
  current : Cursor frame

def fromActual (frame : CPS1Recycling.Frame) (previous : Current.Occurrence frame) : Occurrence frame :=
  ⟨previous,start frame previous⟩

def execution (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat) (actions : List RawAction) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← Current.execution edits water additional path recycleFeed scanFeed bodyFeed depth
  let current := fromActual previous.1 previous.2
  pure ⟨previous.1,{current with current := advance previous.1 current.current actions}⟩

def resume (frame : CPS1Recycling.Frame) (current : Occurrence frame) (actions : List RawAction) :
    Occurrence frame := {current with current := advance frame current.current actions}

theorem continuation_source (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (actions : List RawAction) : (resume frame current actions).previous = current.previous := rfl

theorem advance_pending (frame : CPS1Recycling.Frame) (cursor : Cursor frame) (actions : List RawAction) :
    (advance frame cursor actions).stages.length = cursor.stages.length+1 := by
  simp only [advance,List.length_append,List.length_singleton]

theorem held_atomic_member (frame : CPS1Recycling.Frame) (stock : Current.Stock frame)
    (chain : Chain frame) (held : heldAtomic frame stock = some chain) :
    Current.Species.atomic chain ∈ stock := by
  induction stock with
  | nil => cases held
  | cons species rest ih =>
    cases species <;> first
    | exact List.mem_cons_of_mem _ (ih held)
    | simp only [heldAtomic,Option.some.injEq] at held
      cases held
      exact List.mem_cons_self

theorem start_current (frame : CPS1Recycling.Frame) (previous : Current.Occurrence frame)
    (chain : Chain frame) (held : heldAtomic frame previous.current.stock = some chain) :
    (start frame previous).stock.Perm (.body ⟨chain,[],0⟩ ::
      (previous.current.stock.erase (.atomic chain)).map Species.retained) ∧
    (start frame previous).captureRemaining = [] ∧ (start frame previous).cut = none := by
  have member := held_atomic_member frame previous.current.stock chain held
  have inventory := (List.perm_cons_erase member).map (Species.retained (frame := frame))
  have result := capture_current frame chain _ _ inventory
  simp only [start,held]
  exact ⟨result.2.2.2,result.2.1,result.2.2.1⟩

end
end CPS1AtomicDynamics.Source
