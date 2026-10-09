import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell1Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel WholeBandActual WholeCellBoundary
open WholeBandCell1Actual WholeBandCell1Source
open Set
noncomputable section

structure WholeBandCell1Material where
  parent : WholeBandCell0SpatialRuntime.WholeBandCell0SpatialMaterial
  parameterMap : Point → Point
  fullFlows : Cell1Point → ℝ → Point
  image : Set Point
  initialResponses : Cell1Point → (Point →L[ℝ] _root_.LAlanineTrueFlowDifferential.Path)
  timeResponses : Cell1Point → _root_.LAlanineTrueFlowDifferential.Time → (Point →L[ℝ] Point)
  jacobians : Cell1Point → (Point →L[ℝ] Point)

def generatedWholeBandCell1Material : WholeBandCell1Material where
  parent := wholeBandCell1ParentMaterial
  parameterMap := WholeBandContinuation.sourceParameterMap 1
  fullFlows := fun p => TrueFlowDifferential.rawFlow (WholeBandGeometry.cellSeed 1 p.val)
  image := cell1_actualImage
  initialResponses := fun p => WholeBandContinuationDifferential.sourceResponse 1 p.val
  timeResponses := fun p => WholeBandContinuationDifferential.initialFlowDerivative 1 p.val
  jacobians := fun p => WholeBandContinuationParameter.trueJacobian 1 p.val

inductive WholeBandCell1Projection
  | material | certificate

def wholeBandCell1ProjectionLaw : SourceNativeProjectionLaw WholeBandCell1Ledger where
  Projection := WholeBandCell1Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt WholeBandCell1Ledger.source occurrence × WholeBandCell1Material
    | .certificate => PLift WholeBandCell1Closure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (WholeBandCell1Ledger.ledgerCompiler.compile occurrence, generatedWholeBandCell1Material)
    | certificate => exact ⟨sourceGeneratedWholeBandCell1Closure⟩

def wholeBandCell1AuthoritySource := WholeBandCell1Base.withProjectionCoface wholeBandCell1ProjectionLaw
def wholeBandCell1ComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt wholeBandCell1ProjectionLaw wholeBandCell1AuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface WholeBandCell1Base wholeBandCell1ProjectionLaw
def wholeBandCell1InheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt WholeBandCell1Base.projectionLaw wholeBandCell1AuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface WholeBandCell1Base wholeBandCell1ProjectionLaw

def wholeBandCell1AuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := wholeBandCell1AuthoritySource
  emitted := WholeBandCell0SpatialRuntime.wholeBandCell0SpatialAuthoritativeRoot.emitted
  compiler_commutes := WholeBandCell0SpatialRuntime.wholeBandCell0SpatialAuthoritativeRoot.compiler_commutes

def wholeBandCell1LivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  wholeBandCell1AuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem wholeBandCell1_source_and_law_unchanged :
    wholeBandCell1AuthoritySource.restructuringSource = WholeBandCell1Base.restructuringSource ∧
    wholeBandCell1AuthoritySource.eventInventoryAdmission = WholeBandCell1Base.eventInventoryAdmission ∧
    wholeBandCell1AuthoritySource.lawSurface = WholeBandCell1Base.lawSurface := ⟨rfl,rfl,rfl⟩

theorem wholeBandCell1_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    wholeBandCell1AuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      WholeBandCell0SpatialRuntime.wholeBandCell0SpatialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandCell1Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
