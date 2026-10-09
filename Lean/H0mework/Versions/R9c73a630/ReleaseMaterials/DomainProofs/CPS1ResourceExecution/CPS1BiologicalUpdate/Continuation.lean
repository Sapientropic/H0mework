import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Birth

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1ReactiveSourceEntry CPS1LiveEditing
variable {frame : CPS1Recycling.Frame}

structure ContinuationRaw where
  water : Nat
  translation : List RawSupply
  path : CPS1Recycling.SplitSite
  recycling : List CPS1Recycling.RawEvent
  recycleFeed : List CPS1Recycling.RawMaterial
  physical : PhysicalRaw
  depth : Nat

structure ContinuedBiosynthesis {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth)
    (supply : ContinuationRaw) where
  next : WholeRun event.reached supply.water supply.translation supply.path
    supply.recycling supply.recycleFeed supply.physical supply.depth
  actual : next = executeWhole event.reached supply.water supply.translation supply.path
    supply.recycling supply.recycleFeed supply.physical supply.depth
  original : next.original = event.reached
  priorBirth : event.newlyProduced =
    (credit event.physicalEvent.seed.translation.native.fired).count
      (.releasedPeptide event.physicalEvent.seed.translation.peptide)

def continueBiosynthesis {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth)
    (supply : ContinuationRaw) : ContinuedBiosynthesis event supply :=
  let next := executeWhole event.reached supply.water supply.translation supply.path
    supply.recycling supply.recycleFeed supply.physical supply.depth
  ⟨next,rfl,next.originalSource,biosynthetic_birth_credit event⟩

def continueActualWhole {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (whole : WholeRun before water raw path events feed physical depth) (supply : ContinuationRaw) :
    Sum (BiosyntheticDisposition before water raw path events feed physical depth)
      (Σ event : NativeBiosyntheticEvent before water raw path events feed physical depth,
        ContinuedBiosynthesis event supply) :=
  match consumeWhole whole with
  | .sourceResidual original => .inl (.sourceResidual original)
  | .produced event => .inr ⟨event,continueBiosynthesis event supply⟩

theorem continuation_reads_actual_current {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth)
    (supply : ContinuationRaw) :
    (continueBiosynthesis event supply).next.original = event.reached ∧
    (continueBiosynthesis event supply).next.original.native.current = event.reached.native.current ∧
    HEq (continueBiosynthesis event supply).next.original.germ event.reached.germ := by
  have whole := whole_run_original event.reached supply.water supply.translation supply.path
    supply.recycling supply.recycleFeed supply.physical supply.depth
  exact ⟨whole.1,congrArg (fun cursor => cursor.current) whole.2.1,whole.2.2⟩

end
end CPS1BiologicalUpdate
