import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionPaid.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionLedger.Runtime.Consumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionPaid.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
open LAlanine40K2025.BasinRefinement.WholeBandBasin
noncomputable section

def parentRuntime := PreciseAttractionLedger.Runtime.afterFirst
def parentMaterial : PreciseAttractionLedger.Material := PreciseAttractionLedger.Runtime.readMaterial parentRuntime
abbrev ParentBase := PreciseAttractionLedger.Runtime.authoritySource
abbrev ParentLedger := ParentBase.restructuringSource.toLedgerSource

inductive Projection
  | material | certificate

def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × PreciseAttractionPaid.Material
    | .certificate => PLift PreciseAttractionPaid.Closure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (ParentLedger.ledgerCompiler.compile occurrence,PreciseAttractionPaid.material)
    | certificate => exact ⟨PreciseAttractionPaid.sourceGeneratedClosure⟩

def authoritySource := ParentBase.withProjectionCoface projectionLaw

def componentInstallation : SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

def inheritedInstallation : SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := authoritySource
  emitted := PreciseAttractionLedger.Runtime.authoritativeRoot.emitted
  compiler_commutes := PreciseAttractionLedger.Runtime.authoritativeRoot.compiler_commutes

def livingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem source_and_law_unchanged :
    authoritySource.restructuringSource = ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission = ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface = ParentBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    authoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      PreciseAttractionLedger.Runtime.authoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionPaid.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
