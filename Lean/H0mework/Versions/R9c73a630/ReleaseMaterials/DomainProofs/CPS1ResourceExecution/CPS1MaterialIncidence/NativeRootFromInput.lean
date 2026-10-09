import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeInput
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRootMaterialData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeRootDataProbe
noncomputable section
open CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate CPS1LiveEditing
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration

def ProgrammeAt (input : RegisteredNativeInput) : Type 1 :=
  Σ frame : CPS1Recycling.Frame, CPS1ReactiveSourceEntry.Programme frame input.firstDepth input.secondDepth

def source_programme (input : RegisteredNativeInput) : Option (ProgrammeAt input) :=
  CPS1ReactiveSourceEntry.programmeFromSource input.edits input.water input.additional input.path
    input.recycleFeed input.scanFeed input.bodyFeed input.depth input.oldActions input.bathActions input.bathFeed
    input.electronicActions input.electronicFeed input.nuclearActions input.nuclearFeed
    input.followingActions input.followingFeed input.molecularActions input.molecularFeed
    input.deformationActions input.deformationFeed input.actions input.feed input.raw
    input.firstDepth input.input input.secondDepth

/-- This higher source is computed from registered primitive input. It is an
index of the stored Type0 body, rather than a dynamic field in the root. -/
structure InputOccurrence (input : RegisteredNativeInput) : Type 1 where
  programme : ProgrammeAt input
  whole : WholeRun programme.2.current input.updateWater input.updateRaw input.updatePath
    input.recycleEvents input.recycleRaw input.physical input.newDepth
  wholeActual : whole = executeWhole programme.2.current input.updateWater input.updateRaw input.updatePath
    input.recycleEvents input.recycleRaw input.physical input.newDepth
  repair : LocalRepairDisposition (initialBody ⟨programme.1,programme.2.current⟩)
  repairActual : repair = repairWhole whole input.supply
  response : WholeResponse repair input.response
  responseActual : response = wholeResponse repair input.response
  outcome : CPS1PhosphorylExchange.Disposition input.response input.exchange repair response
  outcomeActual : outcome = fromWhole repair response input.exchange

def generated_input (input : RegisteredNativeInput) : Option (InputOccurrence input) :=
  (source_programme input).map (fun programme =>
    let whole := executeWhole programme.2.current input.updateWater input.updateRaw input.updatePath
      input.recycleEvents input.recycleRaw input.physical input.newDepth
    let repair := repairWhole whole input.supply
    let response := wholeResponse repair input.response
    ⟨programme,whole,rfl,repair,rfl,response,rfl,fromWhole repair response input.exchange,rfl⟩)

theorem generated_input_programme (input : RegisteredNativeInput) :
    (generated_input input).map InputOccurrence.programme = source_programme input := by
  simp only [generated_input,Option.map_map,Function.comp_def]
  cases source_programme input <;> rfl


attribute [local irreducible] generated_input source_programme

def NativeProfile (supply : ContinuationRaw) : Prop :=
  supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply

structure RetainedBodyAt (expected : CPS1PhosphorylExchange.Failure) : Type where
  failure : CPS1PhosphorylExchange.Failure
  actual : failure = expected

section Native
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

structure ProfileResidualAt (supply : ContinuationRaw) (source : Common before step raw)
    (current : NativeCurrent source) : Type where
  native : NativeCurrent source
  actual : native = current
  failed : ¬ NativeProfile supply

end Native

section Disposition
variable {frame : CPS1Recycling.Frame} {origin : CPS1ReactiveNuclear.SourceCursor frame}
  {water : Nat} {material : List RawSupply} {path : CPS1Recycling.SplitSite}
  {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}
  (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
  {responseRaw : WholeRaw} {exchange : CPS1PhosphorylExchange.Raw}
  (repair : LocalRepairDisposition (initialBody ⟨frame,origin⟩))
  (response : WholeResponse repair responseRaw)
  (outcome : CPS1PhosphorylExchange.Disposition responseRaw exchange repair response)
  (repairActual : repair = repairWhole whole supply)

def DispositionBodyAt : Type := by
  classical
  cases outcome with
  | retained response failure => exact RetainedBodyAt failure
  | @responded receipt response before step actual source current =>
    exact if profile : NativeProfile supply then
      let paid := source_paid_data whole supply profile receipt repairActual.symm source current
      let continuation := source_continuation_data paid
      GeneratedBodyAt whole supply profile receipt repairActual.symm source paid continuation
    else ProfileResidualAt supply source current

def source_disposition_body : DispositionBodyAt whole supply repair response outcome repairActual := by
  classical
  cases outcome with
  | retained response failure => exact ⟨failure,rfl⟩
  | @responded receipt response before step actual source current =>
    dsimp only [DispositionBodyAt]
    split
    · rename_i profile
      exact source_generated_body_at whole supply profile receipt repairActual.symm source
        (source_paid_data whole supply profile receipt repairActual.symm source current)
        (source_continuation_data (source_paid_data whole supply profile receipt repairActual.symm source current))
    · rename_i failed
      exact ⟨current,rfl,failed⟩

def disposition_body_next (body : DispositionBodyAt whole supply repair response outcome repairActual) :
    DispositionBodyAt whole supply repair response outcome repairActual := by
  classical
  cases outcome with
  | retained response failure => exact body
  | @responded receipt response before step actual source current =>
    by_cases profile : NativeProfile supply
    · simp only [DispositionBodyAt,dif_pos profile] at body ⊢
      exact body_next receipt body
    · exact body

end Disposition

structure MissingProgrammeAt (input : RegisteredNativeInput) : Type where
  actual : generated_input input = none

def InputBodyAt (input : RegisteredNativeInput) : Type :=
  match generated_input input with
  | none => MissingProgrammeAt input
  | some occurrence => DispositionBodyAt occurrence.whole input.supply occurrence.repair
      occurrence.response occurrence.outcome occurrence.repairActual

def source_input_body (input : RegisteredNativeInput) : InputBodyAt input := by
  cases actual : generated_input input with
  | none =>
    simp only [InputBodyAt,actual]
    exact ⟨actual⟩
  | some occurrence =>
    simp only [InputBodyAt,actual]
    exact source_disposition_body occurrence.whole input.supply occurrence.repair
      occurrence.response occurrence.outcome occurrence.repairActual

def input_body_next (input : RegisteredNativeInput) (body : InputBodyAt input) : InputBodyAt input := by
  cases actual : generated_input input with
  | none => exact body
  | some occurrence =>
    simp only [InputBodyAt,actual] at body ⊢
    exact disposition_body_next occurrence.whole input.supply occurrence.repair
      occurrence.response occurrence.outcome occurrence.repairActual body

end
end CPS1MaterialIncidence.NativeRootDataProbe
