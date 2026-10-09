import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.ActualRealization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel SourceSignedEvaluator IntervalParameterMap TrueTubeActual
noncomputable section

structure TrueTubeMaterial where
  parent : BoundaryRuntime.BoundaryMaterial
  sourceReceipt : String
  actualBoxes : TrueTubeSource.Field → Rectangle
  certifiedFields : TrueTubeSource.Field → FieldBox
  actualCalls : TrueTubeSource.Call → Rectangle
  initialBoxes : TrueTubeSource.Direction → TrueTubeSource.Step → Rectangle
  tubeBoxes : TrueTubeSource.Direction → TrueTubeSource.Step → Rectangle
  endpointBoxes : TrueTubeSource.Direction → TrueTubeSource.Step → Rectangle
  signs : TrueTubeSource.Direction → ℚ
  stepSize : ℚ
  elapsedStarts : TrueTubeSource.Direction → TrueTubeSource.Step → ℚ
  elapsedStops : TrueTubeSource.Direction → TrueTubeSource.Step → ℚ
  firstCurves : (d : TrueTubeSource.Direction) → InitialAt d → ℝ → Point
  firstTargets : (d : TrueTubeSource.Direction) → InitialAt d → TargetAt d

def generatedTrueTubeMaterial : TrueTubeMaterial where
  parent := tubeParentMaterial
  sourceReceipt := TrueTubeSource.packetText
  actualBoxes := TrueTubeSource.box
  certifiedFields := TrueTubeSource.recordedField
  actualCalls := TrueTubeSource.callBox
  initialBoxes := TrueTubeSource.initialBox
  tubeBoxes := TrueTubeSource.tubeBox
  endpointBoxes := TrueTubeSource.endpointBox
  signs := TrueTubeSource.sign
  stepSize := TrueTubeSource.stepSize
  elapsedStarts := TrueTubeSource.elapsedStart
  elapsedStops := TrueTubeSource.elapsedStop
  firstCurves := firstCurve
  firstTargets := firstTarget

inductive TrueTubeProjection
  | material | certificate

def tubeProjectionLaw : SourceNativeProjectionLaw TubeLedger where
  Projection := TrueTubeProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt TubeLedger.source occurrence × TrueTubeMaterial
    | .certificate => PLift FirstContinuationClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (TubeLedger.ledgerCompiler.compile occurrence, generatedTrueTubeMaterial)
    | certificate => exact ⟨sourceGeneratedFirstContinuationClosure⟩

def tubeAuthoritySource := TubeBase.withProjectionCoface tubeProjectionLaw
def tubeComponentInstallation : SourceNativeProjectionLaw.InstallationAt tubeProjectionLaw tubeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface TubeBase tubeProjectionLaw
def tubeInheritedInstallation : SourceNativeProjectionLaw.InstallationAt TubeBase.projectionLaw tubeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface TubeBase tubeProjectionLaw

def tubeAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := tubeAuthoritySource
  emitted := BoundaryRuntime.boundaryAuthoritativeRoot.emitted
  compiler_commutes := BoundaryRuntime.boundaryAuthoritativeRoot.compiler_commutes

def tubeLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  tubeAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem tube_source_and_law_unchanged :
    tubeAuthoritySource.restructuringSource = TubeBase.restructuringSource ∧
    tubeAuthoritySource.eventInventoryAdmission = TubeBase.eventInventoryAdmission ∧
    tubeAuthoritySource.lawSurface = TubeBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem tube_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    tubeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      BoundaryRuntime.boundaryAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.TrueTubeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
