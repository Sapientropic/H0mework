import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.Continuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EditingChemicalJoin.GenericStock
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EditingChemicalJoin.EditingStock

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1EditingChemicalJoin.Source
open CPS1ResourceExecution
open CPS1LocalChemicalExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RawMaterial | atp | bicarbonate | water | processor deriving DecidableEq

def RawMaterial.local : RawMaterial → CPS1LocalChemicalExecution.Source.RawMaterial
  | .atp => .molecule .atp
  | .bicarbonate => .molecule .bicarbonate
  | .water => .molecule .water
  | .processor => .processor

def editingSpecies (frame : CPS1Recycling.Frame) (species : CPS1ResourceExecution.Species) : Species frame :=
  .retained (CPS1StockRecursion.Dictionary.old frame species)

structure Occurrence (frame : CPS1Recycling.Frame) where
  previous : CPS1LocalChemicalExecution.Source.Occurrence frame
  editingFirst : CPS1ResourceExecution.Execution
  editing : CPS1ResourceExecution.Execution
  current : CPS1LocalChemicalExecution.Source.Cursor frame

def fromActual (frame : CPS1Recycling.Frame) (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) : Occurrence frame :=
  let first := CPS1Deamination.ExecutionReadout.sourceExecution edits water
  let editing := CPS1Deamination.Continuation.sourceContinuation edits water additional
  ⟨previous,first,editing,{previous.current with
    stock := previous.current.stock ++ editing.stock.map (editingSpecies frame)}⟩

/-- A continuation consumes the joined current and its pending program. It never
re-enters either source generator or copies the previous editing inventory. -/
def advance (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction) (feed : List RawMaterial) : Occurrence frame :=
  let next := CPS1LocalChemicalExecution.Source.advance frame current.current actions (feed.map RawMaterial.local)
  {current with current := next}

def execution (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial)
    (scanFeed : List CPS1Reinitiation.RawMaterial) (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial)
    (depth : Nat) (actions : List CPS1LocalChemicalExecution.Source.LocalAction) (feed : List RawMaterial) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1LocalChemicalExecution.Source.actualCapture edits water additional path
    recycleFeed scanFeed bodyFeed depth
  let joined := fromActual previous.1 previous.2 edits water additional
  pure ⟨previous.1,advance previous.1 joined
    (actions ++ CPS1LocalChemicalExecution.Source.chemicalActions) feed⟩

def rawFuel : List RawMaterial := [.atp,.atp,.bicarbonate]

theorem editing_ammonia_is_shared (frame : CPS1Recycling.Frame) :
    editingSpecies frame CPS1ResourceExecution.Species.ammonia = molecule frame .ammonia := rfl

theorem actual_join_stock (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) :
    let joined := fromActual frame previous edits water additional
    joined.current.stock = previous.current.stock ++
      (CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.map (editingSpecies frame) ∧
    joined.editingFirst = CPS1Deamination.ExecutionReadout.sourceExecution edits water ∧
    joined.editing = CPS1Deamination.Continuation.sourceContinuation edits water additional ∧
    joined.current.pending = previous.current.pending := ⟨rfl,rfl,rfl,rfl⟩

theorem from_actual_paid_editing (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) :
    let joined := fromActual frame previous edits water additional
    joined.editing.stock = CPS1Deamination.ExecutionReadout.workingStock
      (CPS1Deamination.ExecutionReadout.prefixWord CPS1Deamination.Source.originalMinusAligned
        ((CPS1Deamination.Source.sourceProgram edits).steps.take (water+additional)))
      (min (water+additional) (CPS1Deamination.Source.sourceProgram edits).steps.length)
      (water+additional-(CPS1Deamination.Source.sourceProgram edits).steps.length) :=
  (CPS1Deamination.Continuation.source_continuation_update edits water additional).2.2.1

theorem advance_chemical_complete (frame : CPS1Recycling.Frame) (current : Occurrence frame)
    (present : molecule frame .ammonia ∈ current.current.stock)
    (captured : current.current.captureRemaining = []) (pending : current.current.pending = []) :
    let next := advance frame current CPS1LocalChemicalExecution.Source.chemicalActions rawFuel
    next.current.stock.Perm (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
      current.current.stock.erase (molecule frame .ammonia)) ∧
    next.current.captureRemaining = [] ∧ next.current.pending = [] ∧ next.current.cut = none ∧
    next.previous = current.previous ∧ next.editingFirst = current.editingFirst ∧ next.editing = current.editing := by
  have paid := CPS1EditingChemicalJoin.consume_existing_ammonia frame current.current.stock present
  dsimp only
  simp only [advance,CPS1LocalChemicalExecution.Source.advance,captured,pending,List.nil_append,List.append_nil,
    rawFuel,List.map_cons,List.map_nil,
    RawMaterial.local,CPS1LocalChemicalExecution.Source.RawMaterial.species,
    CPS1LocalChemicalExecution.Source.chemicalActions,List.flatMap_cons,List.flatMap_nil,
    CPS1LocalChemicalExecution.Source.LocalAction.material]
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨paid.2.2.2,?_,?_,paid.2.2.1,True.intro,True.intro,True.intro⟩
  · exact List.drop_nil
  · change List.drop ((execute frame (CPS1LocalChemicalExecution.Source.chemistryProgram frame)
        (current.current.stock ++ externalSubstrates frame)).fired.length - 0)
        CPS1LocalChemicalExecution.Source.chemicalActions = []
    rw [paid.1]
    simp only [List.length_nil,Nat.sub_zero,CPS1LocalChemicalExecution.Source.chemistryProgram,
      List.length_cons]
    rfl

theorem joined_ammonia (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat)
    (generated : 0 < EditingStock.paid edits water additional) :
    molecule frame .ammonia ∈ (fromActual frame previous edits water additional).current.stock := by
  apply List.mem_append_right
  exact EditingStock.ammonia_present frame edits water additional generated

theorem actual_chemical_from_join (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat)
    (generated : 0 < EditingStock.paid edits water additional)
    (captured : previous.current.captureRemaining = []) (pending : previous.current.pending = []) :
    let joined := fromActual frame previous edits water additional
    let next := advance frame joined CPS1LocalChemicalExecution.Source.chemicalActions rawFuel
    next.current.stock.Perm (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
      joined.current.stock.erase (molecule frame .ammonia)) ∧
    next.current.captureRemaining = [] ∧ next.current.pending = [] ∧ next.current.cut = none ∧
    next.previous = previous ∧
    next.editingFirst = CPS1Deamination.ExecutionReadout.sourceExecution edits water ∧
    next.editing = CPS1Deamination.Continuation.sourceContinuation edits water additional := by
  exact advance_chemical_complete frame (fromActual frame previous edits water additional)
    (joined_ammonia frame previous edits water additional generated) captured pending

theorem execution_from_actual_capture (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial)
    (scanFeed : List CPS1Reinitiation.RawMaterial) (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial)
    (depth : Nat) (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (actual : CPS1LocalChemicalExecution.Source.actualCapture edits water additional path
      recycleFeed scanFeed bodyFeed depth = some ⟨frame,previous⟩)
    (generated : 0 < EditingStock.paid edits water additional)
    (captured : previous.current.captureRemaining = []) (pending : previous.current.pending = []) :
    let joined := fromActual frame previous edits water additional
    let next := advance frame joined CPS1LocalChemicalExecution.Source.chemicalActions rawFuel
    execution edits water additional path recycleFeed scanFeed bodyFeed depth [] rawFuel = some ⟨frame,next⟩ ∧
    next.current.stock.Perm (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
      joined.current.stock.erase (molecule frame .ammonia)) ∧
    next.current.captureRemaining = [] ∧ next.current.pending = [] ∧ next.current.cut = none ∧
    next.previous = previous ∧
    next.editingFirst = CPS1Deamination.ExecutionReadout.sourceExecution edits water ∧
    next.editing = CPS1Deamination.Continuation.sourceContinuation edits water additional := by
  have updated := actual_chemical_from_join frame previous edits water additional generated captured pending
  refine ⟨?_,updated⟩
  simp only [execution,actual,List.nil_append]
  rfl

theorem actual_chemical_complete (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < EditingStock.paid edits water additional) :
    ∃ (frame : CPS1Recycling.Frame) (next : Occurrence frame),
    execution edits water additional path recycleFeed scanFeed bodyFeed depth [] rawFuel = some ⟨frame,next⟩ ∧
    next.current.stock.Perm (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
      (fromActual frame next.previous edits water additional).current.stock.erase (molecule frame .ammonia)) ∧
    next.current.captureRemaining = [] ∧ next.current.pending = [] ∧ next.current.cut = none ∧
    next.editingFirst = CPS1Deamination.ExecutionReadout.sourceExecution edits water ∧
    next.editing = CPS1Deamination.Continuation.sourceContinuation edits water additional := by
  have captured := CPS1LocalChemicalExecution.Source.actual_capture_complete edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  dsimp only at captured
  rcases captured with ⟨actual,inventory,ready,noCut⟩
  have paid := execution_from_actual_capture edits water additional path recycleFeed scanFeed bodyFeed depth
    _ _ actual generated ready rfl
  refine ⟨_,_,paid.1,?_,paid.2.2.1,paid.2.2.2.1,paid.2.2.2.2.1,paid.2.2.2.2.2.2.1,paid.2.2.2.2.2.2.2⟩
  exact paid.2.1

end CPS1EditingChemicalJoin.Source
