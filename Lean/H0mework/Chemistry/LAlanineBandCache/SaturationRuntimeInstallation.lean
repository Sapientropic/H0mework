import H0mework.Chemistry.LAlanineBandCache.SaturationRuntimeParent
import H0mework.Chemistry.LAlanineBandCache.SaturationSourceClosure

/-! Install the certified cell2 exponential calculation on the original M3 occurrence, retaining Root60. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

/-- Complete Root60 material and the actual cell2 Gaussian calculation values. -/
structure SaturationMaterial where
  parent : LAlanine40K2025.AtomicMass.Runtime.AtomicMassMaterial
  calculation : Source.Cell2SaturationMaterial

def generatedSaturationMaterial : SaturationMaterial where
  parent := saturationParentMaterial
  calculation := Source.material

inductive SaturationProjection
  | material | certificate

def saturationProjectionLaw : SourceNativeProjectionLaw SaturationLedger where
  Projection := SaturationProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt SaturationLedger.source occurrence × SaturationMaterial
    | .certificate => PLift Source.Cell2SaturationClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (SaturationLedger.ledgerCompiler.compile occurrence, generatedSaturationMaterial)
    | certificate => exact ⟨Source.sourceGeneratedCell2SaturationClosure⟩

def saturationAuthoritySource := SaturationBase.withProjectionCoface saturationProjectionLaw
def saturationComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt saturationProjectionLaw saturationAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface SaturationBase saturationProjectionLaw
def saturationInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt SaturationBase.projectionLaw saturationAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface SaturationBase saturationProjectionLaw

def saturationAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := saturationAuthoritySource
  emitted := LAlanine40K2025.AtomicMass.Runtime.atomicMassAuthoritativeRoot.emitted
  compiler_commutes := LAlanine40K2025.AtomicMass.Runtime.atomicMassAuthoritativeRoot.compiler_commutes

def saturationLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  saturationAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem saturation_source_and_law_unchanged :
    saturationAuthoritySource.restructuringSource = SaturationBase.restructuringSource ∧
    saturationAuthoritySource.eventInventoryAdmission = SaturationBase.eventInventoryAdmission ∧
    saturationAuthoritySource.lawSurface = SaturationBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem saturation_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    saturationAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      LAlanine40K2025.AtomicMass.Runtime.atomicMassAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandSaturation.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule