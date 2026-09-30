import H0mework.Chemistry.LAlanineBandCellDifferential.RuntimeParent
import H0mework.Chemistry.LAlanineBandCellDifferential.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.LAlanineTrueFlowDifferential
open LAlanine40K2025.Root SourceGaussianModel WholeBandActual TrueFlowDifferential
open WholeBandCell0Differential WholeBandCell0DifferentialSource
noncomputable section

structure WholeBandCell0DifferentialMaterial where
  parent : WholeBandCell0Runtime.WholeBandCell0Material
  responses : Cell0Point → Space →L[ℝ] Path
  initialDerivatives : Cell0Point → Time → Space →L[ℝ] Space
  jacobians : Cell0Point → Point →L[ℝ] Point
  seedFrames : Cell0Point → Point →L[ℝ] Point
  responseEquivalences : Cell0Point → Time → Point ≃L[ℝ] Point
  jacobianEquivalences : Cell0Point → Point ≃L[ℝ] Point
  scaledPaths : Cell0Point → Path
  scaledResponses : Cell0Point → InitialScale →L[ℝ] Path
  parameterInputs : Point → InitialScale

def generatedWholeBandCell0DifferentialMaterial : WholeBandCell0DifferentialMaterial where
  parent := wholeBandCell0DifferentialParentMaterial
  responses := cell0_sourceResponse
  initialDerivatives := cell0_initialFlowDerivative
  jacobians := cell0_trueJacobian
  seedFrames := cell0_seedFlowDerivative
  responseEquivalences := cell0_initialFlowDerivativeEquiv
  jacobianEquivalences := cell0_trueJacobianEquiv
  scaledPaths := cell0_scaledActualPath
  scaledResponses := cell0_scaledResponse
  parameterInputs := cell0_parameterInput

inductive WholeBandCell0DifferentialProjection
  | material | certificate

def wholeBandCell0DifferentialProjectionLaw : SourceNativeProjectionLaw WholeBandCell0DifferentialLedger where
  Projection := WholeBandCell0DifferentialProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt WholeBandCell0DifferentialLedger.source occurrence × WholeBandCell0DifferentialMaterial
    | .certificate => PLift WholeBandCell0DifferentialClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (WholeBandCell0DifferentialLedger.ledgerCompiler.compile occurrence, generatedWholeBandCell0DifferentialMaterial)
    | certificate => exact ⟨sourceGeneratedWholeBandCell0DifferentialClosure⟩

def wholeBandCell0DifferentialAuthoritySource := WholeBandCell0DifferentialBase.withProjectionCoface wholeBandCell0DifferentialProjectionLaw
def wholeBandCell0DifferentialComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt wholeBandCell0DifferentialProjectionLaw wholeBandCell0DifferentialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface WholeBandCell0DifferentialBase wholeBandCell0DifferentialProjectionLaw
def wholeBandCell0DifferentialInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt WholeBandCell0DifferentialBase.projectionLaw wholeBandCell0DifferentialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface WholeBandCell0DifferentialBase wholeBandCell0DifferentialProjectionLaw

def wholeBandCell0DifferentialAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := wholeBandCell0DifferentialAuthoritySource
  emitted := WholeBandCell0Runtime.wholeBandCell0AuthoritativeRoot.emitted
  compiler_commutes := WholeBandCell0Runtime.wholeBandCell0AuthoritativeRoot.compiler_commutes

def wholeBandCell0DifferentialLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  wholeBandCell0DifferentialAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem wholeBandCell0Differential_source_and_law_unchanged :
    wholeBandCell0DifferentialAuthoritySource.restructuringSource = WholeBandCell0DifferentialBase.restructuringSource ∧
    wholeBandCell0DifferentialAuthoritySource.eventInventoryAdmission = WholeBandCell0DifferentialBase.eventInventoryAdmission ∧
    wholeBandCell0DifferentialAuthoritySource.lawSurface = WholeBandCell0DifferentialBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem wholeBandCell0Differential_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    wholeBandCell0DifferentialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      WholeBandCell0Runtime.wholeBandCell0AuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
