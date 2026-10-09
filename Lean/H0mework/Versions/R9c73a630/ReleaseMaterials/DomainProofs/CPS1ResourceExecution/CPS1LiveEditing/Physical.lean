import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Admission

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
variable {frame : CPS1Recycling.Frame}

structure PhysicalRaw where
  atomicActions : List CPS1AtomicDynamics.Source.RawAction
  bathActions : List CPS1EnzymeBath.Source.RawAction
  bathFeed : List CPS1EnzymeBath.Primary.TemplateKind
  electronicActions : List CPS1ElectronicSource.Source.RawAction
  electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind
  nuclearActions : List CPS1QuantumNuclear.Source.RawAction
  nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind
  followingActions : List CPS1Following.Source.RawAction
  followingFeed : List CPS1EnzymeBath.Primary.TemplateKind
  molecularActions : List CPS1MolecularFrame.Source.RawAction
  molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind
  deformationActions : List CPS1Deformation.Source.RawAction
  deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind
  actions : List CPS1LocalChemicalExecution.Source.LocalAction
  feed : List CPS1LocalChemicalExecution.Source.RawMaterial
  rows : List CPS1AddressedReactiveJoint.Rows.RawAction

structure PhysicalEvent (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw) where
  seed : SourceSeed before.native.current water raw path events feed
  atomic : CPS1AtomicDynamics.Source.Occurrence seed.translation.generatedFrame
  atomicSource : atomic = CPS1AtomicDynamics.Source.resume seed.translation.generatedFrame
    (CPS1AtomicDynamics.Source.fromActual seed.translation.generatedFrame seed.atomic) physical.atomicActions
  bath : CPS1EnzymeBath.Source.Occurrence seed.translation.generatedFrame
  bathSource : bath = CPS1EnzymeBath.Source.resume seed.translation.generatedFrame
    (CPS1EnzymeBath.Source.fromActual seed.translation.generatedFrame atomic)
    (CPS1EnzymeBath.Source.generatedPartnerProgram ++ physical.bathActions) physical.bathFeed
  electronic : CPS1ElectronicSource.Source.Occurrence seed.translation.generatedFrame
  electronicSource : electronic = CPS1ElectronicSource.Source.resume seed.translation.generatedFrame
    (CPS1ElectronicSource.Source.fromActual seed.translation.generatedFrame bath)
    physical.electronicActions physical.electronicFeed
  nuclear : CPS1QuantumNuclear.Source.Occurrence seed.translation.generatedFrame
  nuclearSource : nuclear = CPS1QuantumNuclear.Source.resume seed.translation.generatedFrame
    (CPS1QuantumNuclear.Source.fromActual seed.translation.generatedFrame electronic)
    physical.nuclearActions physical.nuclearFeed
  following : CPS1Following.Source.Occurrence seed.translation.generatedFrame
  followingSource : following = CPS1Following.Source.resume seed.translation.generatedFrame
    (CPS1Following.Source.fromActual seed.translation.generatedFrame nuclear)
    physical.followingActions physical.followingFeed
  molecular : CPS1MolecularFrame.Source.Occurrence seed.translation.generatedFrame
  molecularSource : molecular = CPS1MolecularFrame.Source.resume seed.translation.generatedFrame
    (CPS1MolecularFrame.Source.fromActual seed.translation.generatedFrame following)
    physical.molecularActions physical.molecularFeed
  deformation : CPS1Deformation.Source.Occurrence seed.translation.generatedFrame
  deformationSource : deformation = CPS1Deformation.Source.resume seed.translation.generatedFrame
    (CPS1Deformation.Source.fromActual seed.translation.generatedFrame molecular)
    physical.deformationActions physical.deformationFeed
  generatedRows : CPS1ReactiveSourceEntry.NativeSource.GatherStock deformation.current.stock
  entry : CPS1ReactiveSourceEntry.Entry seed.translation.generatedFrame
  actualEntry : entry = CPS1ReactiveSourceEntry.enterFromOld deformation physical.actions physical.feed physical.rows
  remainder : List (CPS1ReactiveField.LiveMaterial frame)
  remainderSource : remainder = seed.remainder

def physicalEvent (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw)
    (seed : SourceSeed before.native.current water raw path events feed) :
    PhysicalEvent before water raw path events feed physical :=
  let f := seed.translation.generatedFrame
  let atomic := CPS1AtomicDynamics.Source.resume f (CPS1AtomicDynamics.Source.fromActual f seed.atomic) physical.atomicActions
  let bath := CPS1EnzymeBath.Source.resume f (CPS1EnzymeBath.Source.fromActual f atomic)
    (CPS1EnzymeBath.Source.generatedPartnerProgram ++ physical.bathActions) physical.bathFeed
  let electronic := CPS1ElectronicSource.Source.resume f (CPS1ElectronicSource.Source.fromActual f bath)
    physical.electronicActions physical.electronicFeed
  let nuclear := CPS1QuantumNuclear.Source.resume f (CPS1QuantumNuclear.Source.fromActual f electronic)
    physical.nuclearActions physical.nuclearFeed
  let following := CPS1Following.Source.resume f (CPS1Following.Source.fromActual f nuclear)
    physical.followingActions physical.followingFeed
  let molecular := CPS1MolecularFrame.Source.resume f (CPS1MolecularFrame.Source.fromActual f following)
    physical.molecularActions physical.molecularFeed
  let deformation := CPS1Deformation.Source.resume f (CPS1Deformation.Source.fromActual f molecular)
    physical.deformationActions physical.deformationFeed
  let generatedRows := CPS1ReactiveSourceEntry.NativeSource.from_actual_advance_gather
    (frame := f) molecular physical.deformationActions physical.deformationFeed
  let entry := CPS1ReactiveSourceEntry.enterFromOld deformation physical.actions physical.feed physical.rows
  ⟨seed,atomic,rfl,bath,rfl,electronic,rfl,nuclear,rfl,following,rfl,molecular,rfl,deformation,rfl,
    generatedRows,entry,rfl,seed.remainder,rfl⟩

inductive WholeDisposition (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw)
  | rejected (original : SourceDisposition before.native.current water raw path events feed)
  | generated (event : PhysicalEvent before water raw path events feed physical)

def wholeUpdate (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw) :
    WholeDisposition before water raw path events feed physical :=
  match generateSource before.native.current water raw path events feed with
  | SourceDisposition.rejected original => .rejected (.rejected original)
  | SourceDisposition.generated seed => .generated (physicalEvent before water raw path events feed physical seed)

end
end CPS1LiveEditing
