import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

abbrev WholeSection {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) (targets : TargetSection source) :=
  (point : Sigma source.toRootSource.actual.OccurrenceAt) →
    LedgerFor source point.2 (source.toRootSource.actual.compile point.2) (targets point)

def WholeSectionCheck {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    {source : SourceNativeSource N V} (coordinates : Coordinates source)
    (ledgerCoordinates : LedgerCoordinates N) (targets : TargetSection source) (material : M) : Prop :=
  ∀ point : Sigma source.toRootSource.actual.OccurrenceAt,
    WholeCheck ledgerCoordinates source material (coordinates.occurrence point) point.2
      (source.toRootSource.actual.compile point.2) (targets point)

def generatedWhole {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    {source : SourceNativeSource N V} (coordinates : Coordinates source)
    (ledgerCoordinates : LedgerCoordinates N) (targets : TargetSection source) (material : M)
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
  let parts := MotherHigherLawValue.split material
  formWholeParts parts.1 parts.2

abbrev CompilationSection {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) :=
  (point : Sigma source.toRootSource.actual.OccurrenceAt) → SourceNativeLedgerEvolutionAt source point.2

def compilationFromWhole {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) (targets : TargetSection source) (ledgers : WholeSection source targets) :
    CompilationSection source := fun point =>
  (compilationEquiv source point.2).symm
    ((bodyEquiv source point.2 (source.toRootSource.actual.compile point.2)).symm ⟨targets point, ledgers point⟩)

def formCompilation (material : M) : Option (Σ source : SourceValue, CompilationSection source.2.2) :=
  (formWhole material).map (fun ⟨source, targets, ledgers⟩ => ⟨source, compilationFromWhole source.2.2 targets ledgers⟩)

theorem whole_compilation_readback {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) (targets : TargetSection source) (ledgers : WholeSection source targets)
    (point : Sigma source.toRootSource.actual.OccurrenceAt) :
    bodyEquiv source point.2 (source.toRootSource.actual.compile point.2)
      (compilationEquiv source point.2 (compilationFromWhole source targets ledgers point)) =
        ⟨targets point, ledgers point⟩ := by
  rw [compilationFromWhole, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
