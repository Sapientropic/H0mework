import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Exact

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
    (coordinates : ReceiptCoordinates law.vocabulary) (world : LedgerCoordinates N)

def formEvent {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    (compiled : SourceNativeLedgerEvolutionAt source event) (material : M) :
    Option (SourceNativeLedgerRestructuringCertificationAt law compiled) := by
  cases compiled with
  | nativeWrite _ _ _ evolution => exact formExact evolution coordinates world material
  | relationWrite _ _ _ evolution => exact formExact evolution coordinates world material
  | continuedTransport _ _ _ evolution => exact formExact evolution coordinates world material
  | borromeanRedirect _ _ _ evolution => exact formExact evolution coordinates world material
  | faithfulTerminal => exact some PUnit.unit

theorem every_event {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    (compiled : SourceNativeLedgerEvolutionAt source event) (original : SourceNativeLedgerRestructuringCertificationAt law compiled) :
    ∃ material : M, formEvent coordinates world compiled material = some original := by
  cases compiled with
  | nativeWrite _ _ _ evolution => exact every_exact evolution coordinates world original
  | relationWrite _ _ _ evolution => exact every_exact evolution coordinates world original
  | continuedTransport _ _ _ evolution => exact every_exact evolution coordinates world original
  | borromeanRedirect _ _ _ evolution => exact every_exact evolution coordinates world original
  | faithfulTerminal => cases original; exact ⟨MotherHigherLawValue.scalar 0, rfl⟩

variable (points : Coordinates source) (compiled : CompilationSection source)

abbrev CertificationSection := (point : Point source) → SourceNativeLedgerRestructuringCertificationAt law (compiled point)

def certificateAt (material : M) (point : Point source) :
    Option (SourceNativeLedgerRestructuringCertificationAt law (compiled point)) :=
  formEvent coordinates world (compiled point) (MotherHigherLawFamily.family material (points.occurrence point))

def formCertificationSection (material : M) : Option (CertificationSection (law := law) compiled) :=
  if total : ∀ point, ∃ value, certificateAt coordinates world points compiled material point = some value then
    some (fun point => Classical.choose (total point))
  else none

/-- Higher-law family formation pays the complete nonuniform certificate
section. Only actual source points need addresses; neither certificates nor
their function space are submitted as addressable primitive carriers. -/
theorem every_certification_section (original : CertificationSection (law := law) compiled) :
    ∃ material : M, formCertificationSection coordinates world points compiled material = some original := by
  have pointwise := fun point => every_event coordinates world (compiled point) (original point)
  choose materials formed using pointwise
  let fallback : B → M := fun _ => MotherHigherLawValue.scalar 0
  obtain ⟨material, allMaterials⟩ := MotherHigherLawFamily.every_family (Function.extend points.occurrence materials fallback)
  have exactAt (point : Point source) : certificateAt coordinates world points compiled material point = some (original point) := by
    have atPoint := (congrFun allMaterials (points.occurrence point)).trans
      (points.occurrence.injective.extend_apply materials fallback point)
    exact (congrArg (formEvent coordinates world (compiled point)) atPoint).trans (formed point)
  have total : ∀ point, ∃ value, certificateAt coordinates world points compiled material point = some value :=
    fun point => ⟨original point, exactAt point⟩
  refine ⟨material, ?_⟩
  simp only [formCertificationSection, dif_pos total]
  congr 1
  funext point
  exact Option.some.inj ((Classical.choose_spec (total point)).symm.trans (exactAt point))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
