import H0mework.Chemistry.LAlanineBandFlow.RuntimeParent
import H0mework.Chemistry.LAlanineBandFlow.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel WholeBandSource WholeBandFlowSource
noncomputable section

structure WholeBandFlowMaterial where
  parent : WholeBandRuntime.WholeBandMaterial
  rows : FullBandCell → Direction → Step → WholeBandReplay.Inputs
  curves : (d : Direction) → WholeBandActual.InitialAt d → ℝ → Point
  targets : (d : Direction) → WholeBandActual.InitialAt d → WholeBandActual.TargetAt d
  fullFirstFlows : WholeBandActual.Cell0Point → ℝ → Point
  originalFlowKernel : Point → ℝ → Point

def generatedWholeBandFlowMaterial : WholeBandFlowMaterial where
  parent := wholeBandFlowParentMaterial
  rows := WholeBandReplay.rowInput
  curves := WholeBandActual.firstCurve
  targets := WholeBandActual.firstTarget
  fullFirstFlows := WholeBandActual.fullFlow
  originalFlowKernel := TrueFlowDifferential.rawFlow

inductive WholeBandFlowProjection
  | material | certificate

def wholeBandFlowProjectionLaw : SourceNativeProjectionLaw WholeBandFlowLedger where
  Projection := WholeBandFlowProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt WholeBandFlowLedger.source occurrence × WholeBandFlowMaterial
    | .certificate => PLift WholeBandFlowClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (WholeBandFlowLedger.ledgerCompiler.compile occurrence, generatedWholeBandFlowMaterial)
    | certificate => exact ⟨sourceGeneratedWholeBandFlowClosure⟩

def wholeBandFlowAuthoritySource := WholeBandFlowBase.withProjectionCoface wholeBandFlowProjectionLaw
def wholeBandFlowComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt wholeBandFlowProjectionLaw wholeBandFlowAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface WholeBandFlowBase wholeBandFlowProjectionLaw
def wholeBandFlowInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt WholeBandFlowBase.projectionLaw wholeBandFlowAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface WholeBandFlowBase wholeBandFlowProjectionLaw

def wholeBandFlowAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := wholeBandFlowAuthoritySource
  emitted := WholeBandRuntime.wholeBandAuthoritativeRoot.emitted
  compiler_commutes := WholeBandRuntime.wholeBandAuthoritativeRoot.compiler_commutes

def wholeBandFlowLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  wholeBandFlowAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem wholeBandFlow_source_and_law_unchanged :
    wholeBandFlowAuthoritySource.restructuringSource = WholeBandFlowBase.restructuringSource ∧
    wholeBandFlowAuthoritySource.eventInventoryAdmission = WholeBandFlowBase.eventInventoryAdmission ∧
    wholeBandFlowAuthoritySource.lawSurface = WholeBandFlowBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem wholeBandFlow_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    wholeBandFlowAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      WholeBandRuntime.wholeBandAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
