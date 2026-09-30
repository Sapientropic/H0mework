import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.Exact
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Events

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
open MotherObligationOrigin
open MotherRestructuringReceipts
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
    (coordinates : ReceiptCoordinates (rank := rank) law.vocabulary) (world : MotherArenaCompiler.LedgerCoordinates (rank := rank) N)

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
  | faithfulTerminal => cases original; exact ⟨((MotherArenaHigher.readEquiv rank).symm (fun _ _ => 0)), rfl⟩

variable (points : MotherArenaCompiler.Coordinates (rank := rank) source) (compiled : CompilationSection source)

def certificateAt (material : M) (point : Point source) :
    Option (SourceNativeLedgerRestructuringCertificationAt law (compiled point)) :=
  formEvent coordinates world (compiled point) ((MotherArenaHigher.family rank) material (points.occurrence point))

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
  let fallback : B → M := fun _ => ((MotherArenaHigher.readEquiv rank).symm (fun _ _ => 0))
  obtain ⟨material, allMaterials⟩ := (MotherArenaHigher.familyEquiv rank).surjective (Function.extend points.occurrence materials fallback)
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
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
