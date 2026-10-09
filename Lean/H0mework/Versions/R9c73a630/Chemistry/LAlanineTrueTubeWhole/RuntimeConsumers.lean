import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.RuntimeParentConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap TrueTubeWholeActual TrueTubeActual TrueTubeTrace
open TrueTubeSource TrueTubeWholeChecks ContinuousGradient Set
noncomputable section

theorem wholeTubeRuntime_original_flows :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    (∀ d initial, IsIntegralCurveOn (generatedWholeTubeMaterial.directionalFlows d initial)
      (fun _ => signedGradient (sign d)) (Icc (0 : ℝ) (1 / 2))) ∧
    (∀ p, IsIntegralCurveOn (generatedWholeTubeMaterial.wholeFlows p)
      (fun _ => sourceGradient) (Icc (-(1 / 2) : ℝ) (1 / 2))) :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.original,
    wholeTubeRuntime_sourceCertificate.2.fullOriginal⟩

theorem wholeTubeRuntime_all_actual_endpoints :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    (∀ d initial i, InRectangle (generatedWholeTubeMaterial.parent.endpointBoxes d i)
      (generatedWholeTubeMaterial.directionalFlows d initial (generatedWholeTubeMaterial.offsets i + stepSize))) ∧
    (∀ d initial i, InRectangle (generatedWholeTubeMaterial.parent.initialBoxes d i)
      (generatedWholeTubeMaterial.directionalFlows d initial (generatedWholeTubeMaterial.offsets i))) :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.endpoints,
    wholeTubeRuntime_sourceCertificate.2.initials⟩

theorem wholeTubeRuntime_all_tubes :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    (∀ d initial i t, t ∈ Icc 0 (stepSize : ℝ) →
      InRectangle (generatedWholeTubeMaterial.parent.tubeBoxes d i)
        (generatedWholeTubeMaterial.directionalFlows d initial (t + generatedWholeTubeMaterial.offsets i))) :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.tubes⟩

theorem wholeTubeRuntime_preserves_installed_first :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    (∀ d initial,
      EqOn (generatedWholeTubeMaterial.parent.firstCurves d initial)
        (generatedWholeTubeMaterial.directionalFlows d initial) (Icc 0 (stepSize : ℝ)) ∧
      generatedWholeTubeMaterial.directionalFlows d initial stepSize =
        (generatedWholeTubeMaterial.parent.firstTargets d initial).val) :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.firstPreserved⟩

theorem wholeTubeRuntime_source_and_zero_seam :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    type_of% fullFlow_starts ∧ type_of% fullFlow_stays ∧ type_of% fullFlow_zero_derivative ∧
    type_of% TrueTubeWholeMatrix.all_actual_call_fields :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.fullStarts,
    wholeTubeRuntime_sourceCertificate.2.fullStays, wholeTubeRuntime_sourceCertificate.2.zeroDerivative,
    wholeTubeRuntime_sourceCertificate.2.allFields⟩

theorem wholeTubeRuntime_literal_last_endpoint :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    (∀ d initial, InRectangle (generatedWholeTubeMaterial.parent.endpointBoxes d 15)
      (generatedWholeTubeMaterial.directionalFlows d initial (1 / 2))) :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.finalEndpoint⟩

theorem wholeTubeRuntime_common_source_field :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    (∀ x, InRectangle generatedWholeTubeMaterial.commonBox x →
      FieldHolds generatedWholeTubeMaterial.commonField x) ∧
    Real.exp ((generatedWholeTubeMaterial.commonLipschitz : ℝ) / 2) < (23 / 10 : ℝ) :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.commonField,
    wholeTubeRuntime_sourceCertificate.2.amplification⟩

theorem wholeTubeRuntime_actual_finite_error :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    (∀ p s, s ∈ Icc (-(1 / 2) : ℝ) (1 / 2) →
      dist (TrueTubeError.finiteTrajectory (TrueTubeError.zeroTimeParameters p.val) s)
        (generatedWholeTubeMaterial.wholeFlows p s) ≤
      min (gronwallBound 0 generatedWholeTubeMaterial.commonLipschitz
        generatedWholeTubeMaterial.finiteDefect |s|) generatedWholeTubeMaterial.commonDiameter) :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.fullError⟩

theorem wholeTubeRuntime_error_zero :
    type_of% (wholeTubeRuntimeFace_factorizes wholeTubeRuntimeSeed (.component .certificate)) ∧
    type_of% TrueTubeWholeError.zero_error :=
  ⟨wholeTubeRuntime_sourceCertificate.1, wholeTubeRuntime_sourceCertificate.2.zeroError⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
