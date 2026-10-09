import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell2.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell2.SourceClosure
/-! Install the actual call128/160 full-D3 field on the original M3 occurrence, retaining Root62. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

/-- Complete Root62 material and the actual shared rectangle, AO, full-D3 and field values. -/
structure InitialFieldMaterial where
  parent : WholeBandSaturation.Runtime.SaturationMaterial
  calculation : Source.InitialFieldMaterial

def generatedInitialFieldMaterial : InitialFieldMaterial where
  parent := initialFieldParentMaterial
  calculation := Source.material

inductive InitialFieldProjection
  | material | certificate

def initialFieldProjectionLaw : SourceNativeProjectionLaw InitialFieldLedger where
  Projection := InitialFieldProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt InitialFieldLedger.source occurrence × InitialFieldMaterial
    | .certificate => PLift Source.InitialFieldClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (InitialFieldLedger.ledgerCompiler.compile occurrence, generatedInitialFieldMaterial)
    | certificate => exact ⟨Source.sourceGeneratedInitialFieldClosure⟩

def initialFieldAuthoritySource := InitialFieldBase.withProjectionCoface initialFieldProjectionLaw
def initialFieldComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt initialFieldProjectionLaw initialFieldAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface InitialFieldBase initialFieldProjectionLaw
def initialFieldInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt InitialFieldBase.projectionLaw initialFieldAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface InitialFieldBase initialFieldProjectionLaw

def initialFieldAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := initialFieldAuthoritySource
  emitted := WholeBandSaturation.Runtime.saturationAuthoritativeRoot.emitted
  compiler_commutes := WholeBandSaturation.Runtime.saturationAuthoritativeRoot.compiler_commutes

def initialFieldLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  initialFieldAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem initialField_source_and_law_unchanged :
    initialFieldAuthoritySource.restructuringSource = InitialFieldBase.restructuringSource ∧
    initialFieldAuthoritySource.eventInventoryAdmission = InitialFieldBase.eventInventoryAdmission ∧
    initialFieldAuthoritySource.lawSurface = InitialFieldBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem initialField_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    initialFieldAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      WholeBandSaturation.Runtime.saturationAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandCell2.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
