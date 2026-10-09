import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel SourceSignedEvaluator IntervalParameterMap TrueTubeWholeActual
noncomputable section

structure WholeTubeMaterial where
  parent : TrueTubeRuntime.TrueTubeMaterial
  fields : TrueTubeSource.Call → FieldBox
  directionalFlows : (d : TrueTubeSource.Direction) → TrueTubeActual.InitialAt d → ℝ → Point
  wholeFlows : BandPoint → ℝ → Point
  offsets : TrueTubeSource.Step → ℝ
  commonBox : Fin 3 → Pair
  commonField : FieldBox
  commonLipschitz : NNReal
  finiteDefect : ℝ
  commonDiameter : ℝ

def generatedWholeTubeMaterial : WholeTubeMaterial where
  parent := wholeTubeParentMaterial
  fields := TrueTubeWholeSource.recordedCallField
  directionalFlows := wholeDirectionalFlow
  wholeFlows := fullFlow
  offsets := TrueTubeWholeChecks.stepOffset
  commonBox := TrueTubeHullSource.box
  commonField := TrueTubeHullMatrix.sourceField
  commonLipschitz := TrueTubeHull.lipschitzConstant
  finiteDefect := TrueTubeWholeError.wholeDefectBound
  commonDiameter := TrueTubeWholeError.hullDiameter

inductive WholeTubeProjection
  | material | certificate

def wholeTubeProjectionLaw : SourceNativeProjectionLaw WholeTubeLedger where
  Projection := WholeTubeProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt WholeTubeLedger.source occurrence × WholeTubeMaterial
    | .certificate => PLift WholeContinuationClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (WholeTubeLedger.ledgerCompiler.compile occurrence, generatedWholeTubeMaterial)
    | certificate => exact ⟨sourceGeneratedWholeContinuationClosure⟩

def wholeTubeAuthoritySource := WholeTubeBase.withProjectionCoface wholeTubeProjectionLaw
def wholeTubeComponentInstallation : SourceNativeProjectionLaw.InstallationAt wholeTubeProjectionLaw wholeTubeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface WholeTubeBase wholeTubeProjectionLaw
def wholeTubeInheritedInstallation : SourceNativeProjectionLaw.InstallationAt WholeTubeBase.projectionLaw wholeTubeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface WholeTubeBase wholeTubeProjectionLaw

def wholeTubeAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := wholeTubeAuthoritySource
  emitted := TrueTubeRuntime.tubeAuthoritativeRoot.emitted
  compiler_commutes := TrueTubeRuntime.tubeAuthoritativeRoot.compiler_commutes

def wholeTubeLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  wholeTubeAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem wholeTube_source_and_law_unchanged :
    wholeTubeAuthoritySource.restructuringSource = WholeTubeBase.restructuringSource ∧
    wholeTubeAuthoritySource.eventInventoryAdmission = WholeTubeBase.eventInventoryAdmission ∧
    wholeTubeAuthoritySource.lawSurface = WholeTubeBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem wholeTube_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    wholeTubeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      TrueTubeRuntime.tubeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
