import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Flux.Runtime.Parent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Flux.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Flux.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

structure FluxInstalledMaterial where
  parent : WholeBandBasin.Runtime.BasinInstalledMaterial
  calculation : Flux.FluxMaterial

def generatedMaterial : FluxInstalledMaterial := ⟨parentMaterial,Flux.material⟩
inductive FluxProjection
  | material | certificate

def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := FluxProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × FluxInstalledMaterial
    | .certificate => PLift Flux.FluxClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (ParentLedger.ledgerCompiler.compile occurrence,generatedMaterial)
    | certificate => exact ⟨Flux.sourceGeneratedZeroFlux⟩

def authoritySource := ParentBase.withProjectionCoface projectionLaw

def componentInstallation : SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

def inheritedInstallation : SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := authoritySource
  emitted := WholeBandBasin.Runtime.authoritativeRoot.emitted
  compiler_commutes := WholeBandBasin.Runtime.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem source_and_law_unchanged :
    authoritySource.restructuringSource = ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission = ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface = ParentBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    authoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      WholeBandBasin.Runtime.authoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Flux.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
