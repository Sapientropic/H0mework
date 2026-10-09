import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Runtime.Parent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.SourceClosure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

structure FrameInstalledMaterial where
  parent : BasinRefinement.WholeBandBasin.Flux.Runtime.FluxInstalledMaterial
  calculation : FrameMaterial

def generatedMaterial : FrameInstalledMaterial := ⟨parentMaterial,frameMaterial⟩
inductive FrameProjection
  | material | certificate

def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := FrameProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × FrameInstalledMaterial
    | .certificate => PLift FrameClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (ParentLedger.ledgerCompiler.compile occurrence,generatedMaterial)
    | certificate => exact ⟨sourceGeneratedFrameClosure⟩

def authoritySource := ParentBase.withProjectionCoface projectionLaw

def componentInstallation : SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

def inheritedInstallation : SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := authoritySource
  emitted := BasinRefinement.WholeBandBasin.Flux.Runtime.authoritativeRoot.emitted
  compiler_commutes := BasinRefinement.WholeBandBasin.Flux.Runtime.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem source_and_law_unchanged :
    authoritySource.restructuringSource = ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission = ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface = ParentBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    authoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      BasinRefinement.WholeBandBasin.Flux.Runtime.authoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
