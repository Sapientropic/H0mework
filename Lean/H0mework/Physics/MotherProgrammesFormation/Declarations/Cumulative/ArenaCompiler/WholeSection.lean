import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaCompiler.WholeFactory
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Section

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
open MotherArenaNetwork MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def WholeSectionCheck {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    {source : SourceNativeSource N V} (coordinates : Coordinates (rank := rank) source)
    (ledgerCoordinates : LedgerCoordinates (rank := rank) N) (targets : TargetSection source) (material : M) : Prop :=
  ∀ point : Sigma source.toRootSource.actual.OccurrenceAt,
    WholeCheck ledgerCoordinates source material (coordinates.occurrence point) point.2
      (source.toRootSource.actual.compile point.2) (targets point)

def generatedWhole {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    {source : SourceNativeSource N V} (coordinates : Coordinates (rank := rank) source)
    (ledgerCoordinates : LedgerCoordinates (rank := rank) N) (targets : TargetSection source) (material : M)
    (checked : WholeSectionCheck coordinates ledgerCoordinates targets material) : WholeSection source targets :=
  fun point => whole ledgerCoordinates source material (coordinates.occurrence point) point.2
    (source.toRootSource.actual.compile point.2) (targets point) (checked point)

/-- Every old and new entry is compiled by a source-material graph. These are
full tables; finite row selection and its source-owned patch are separate
fields of the original ledger compiler. -/
def formWholeParts (parent material : M) :
    Option (Σ source : SourceValue, Σ targets : TargetSection source.2.2, WholeSection source.2.2 targets) :=
  (formTargets parent).pbind (fun ⟨source, coordinates, targets⟩ formed =>
    let ledgerCoordinates := ledgerCoordinatesOfTargets parent source coordinates targets formed
    if checked : WholeSectionCheck coordinates ledgerCoordinates targets material then
      some ⟨source, targets, generatedWhole coordinates ledgerCoordinates targets material checked⟩
    else none)

def formWhole (material : M) :
    Option (Σ source : SourceValue, Σ targets : TargetSection source.2.2, WholeSection source.2.2 targets) :=
  let parts := (MotherArenaHigher.split rank) material
  formWholeParts parts.1 parts.2

def formCompilation (material : M) : Option (Σ source : SourceValue, CompilationSection source.2.2) :=
  (formWhole material).map (fun ⟨source, targets, ledgers⟩ => ⟨source, compilationFromWhole source.2.2 targets ledgers⟩)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
