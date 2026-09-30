import H0mework.Chemistry.LAlanineTrueFlowGeometry.RuntimeParentConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator ContinuousGradient ContinuousSeed
open TrueFlowDifferential TrueFlowGeometry TrueTubeWholeActual WholeCellPartition
open Set MeasureTheory Matrix
open scoped Matrix ENNReal
noncomputable section

theorem geometryRuntime_full_source_transverse :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧
    generatedGeometryMaterial.normal = basisVector 0 ⨯₃ basisVector 1 ∧
    (∀ j : Fin 2, generatedGeometryMaterial.normal ⬝ᵥ basisVector j = 0) ∧
    type_of% original_gradient_transverse ∧
    (∀ c, 0 < generatedGeometryMaterial.callLower c) ∧
    (∀ c x, InRectangle (TrueTubeSource.callBox c) x →
      0 < generatedGeometryMaterial.normal ⬝ᵥ sourceGradient x) ∧
    (∀ p t, t ∈ Icc (-(1 / 2) : ℝ) (1 / 2) →
      0 < generatedGeometryMaterial.normal ⬝ᵥ
        sourceGradient (generatedGeometryMaterial.parent.parent.wholeFlows p t)) :=
  ⟨geometryRuntime_sourceCertificate.1, geometryRuntime_sourceCertificate.2.normalIsCross,
    geometryRuntime_sourceCertificate.2.normalOrthogonal,
    geometryRuntime_sourceCertificate.2.initialTransverse, geometryRuntime_sourceCertificate.2.allCallLower,
    geometryRuntime_sourceCertificate.2.allCallTransverse, geometryRuntime_sourceCertificate.2.fullTransverse⟩

theorem geometryRuntime_seed_recovery :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧
    type_of% actual_seed_width_positive ∧ type_of% seedFlowDerivative_injective ∧
    type_of% seed_coordinates_of_eq :=
  ⟨geometryRuntime_sourceCertificate.1, geometryRuntime_sourceCertificate.2.seedWidth,
    geometryRuntime_sourceCertificate.2.seedFrameInjective, geometryRuntime_sourceCertificate.2.seedRecovery⟩

theorem geometryRuntime_actual_response :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧
    (∀ p s, Function.Injective (generatedGeometryMaterial.parent.initialDerivatives p s)) ∧
    type_of% initialFlowDerivative_gradient ∧ type_of% trueJacobian_flow_factorization :=
  ⟨geometryRuntime_sourceCertificate.1, geometryRuntime_sourceCertificate.2.responseInjective,
    geometryRuntime_sourceCertificate.2.gradientTransport, geometryRuntime_sourceCertificate.2.factorization⟩

theorem geometryRuntime_nondegenerate :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧
    (∀ p, Function.Injective (generatedGeometryMaterial.parent.jacobians p)) ∧
    (∀ p s, (generatedGeometryMaterial.responseEquivs p s : Point →L[ℝ] Point) =
      generatedGeometryMaterial.parent.initialDerivatives p s) ∧
    (∀ p, (generatedGeometryMaterial.jacobianEquivs p : Point →L[ℝ] Point) =
      generatedGeometryMaterial.parent.jacobians p) ∧
    (∀ p, LinearMap.det (generatedGeometryMaterial.parent.jacobians p).toLinearMap ≠ 0) :=
  ⟨geometryRuntime_sourceCertificate.1, geometryRuntime_sourceCertificate.2.jacobianInjective,
    geometryRuntime_sourceCertificate.2.responseInverseRecognition,
    geometryRuntime_sourceCertificate.2.jacobianInverseRecognition,
    geometryRuntime_sourceCertificate.2.jacobianDeterminant⟩

theorem geometryRuntime_global_no_fold :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧
    (∀ p, generatedGeometryMaterial.planeRead (generatedGeometryMaterial.parent.parent.wholeFlows p 0) = 0) ∧
    (∀ p, StrictMonoOn (fun t => generatedGeometryMaterial.planeRead
      (generatedGeometryMaterial.parent.parent.wholeFlows p t)) (Icc (-(1 / 2) : ℝ) (1 / 2))) ∧
    type_of% fullFlow_meeting_time_eq ∧
    InjOn generatedGeometryMaterial.parent.parameterMap fullDomain :=
  ⟨geometryRuntime_sourceCertificate.1, geometryRuntime_sourceCertificate.2.sectionInitial,
    geometryRuntime_sourceCertificate.2.sectionMonotone, geometryRuntime_sourceCertificate.2.sameTime,
    geometryRuntime_sourceCertificate.2.parameterInjective⟩

theorem geometryRuntime_actual_image :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧
    (∀ p, generatedGeometryMaterial.derivative p.val = generatedGeometryMaterial.parent.jacobians p) ∧
    IsCompact generatedGeometryMaterial.spatialImage ∧ generatedGeometryMaterial.spatialImage.Nonempty ∧
    MeasurableSet generatedGeometryMaterial.spatialImage :=
  ⟨geometryRuntime_sourceCertificate.1, geometryRuntime_sourceCertificate.2.uniqueDerivative,
    geometryRuntime_sourceCertificate.2.imageCompact, geometryRuntime_sourceCertificate.2.imageNonempty,
    geometryRuntime_sourceCertificate.2.imageMeasurable⟩

theorem geometryRuntime_spatial_change_of_variables :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧
    (∀ g : Point → ℝ, (∫ x in generatedGeometryMaterial.spatialImage, g x) =
      ∫ p in fullDomain, |(generatedGeometryMaterial.derivative p).det| •
        g (generatedGeometryMaterial.parent.parameterMap p)) ∧
    (∀ g : Point → ℝ, IntegrableOn g generatedGeometryMaterial.spatialImage ↔
      IntegrableOn (fun p => |(generatedGeometryMaterial.derivative p).det| •
        g (generatedGeometryMaterial.parent.parameterMap p)) fullDomain) ∧
    (∀ g : Point → ℝ≥0∞, (∫⁻ x in generatedGeometryMaterial.spatialImage, g x) =
      ∫⁻ p in fullDomain, ENNReal.ofReal |(generatedGeometryMaterial.derivative p).det| *
        g (generatedGeometryMaterial.parent.parameterMap p)) :=
  ⟨geometryRuntime_sourceCertificate.1, geometryRuntime_sourceCertificate.2.spatialIntegral,
    geometryRuntime_sourceCertificate.2.integrability, geometryRuntime_sourceCertificate.2.nonnegativeIntegral⟩

theorem geometryRuntime_positive_finite_volume :
    type_of% (geometryRuntimeFace_factorizes geometryRuntimeSeed (.component .certificate)) ∧
    volume generatedGeometryMaterial.spatialImage =
      ∫⁻ p in fullDomain, ENNReal.ofReal |(generatedGeometryMaterial.derivative p).det| ∧
    0 < volume generatedGeometryMaterial.spatialImage ∧
    volume generatedGeometryMaterial.spatialImage < ⊤ :=
  ⟨geometryRuntime_sourceCertificate.1, geometryRuntime_sourceCertificate.2.volumeJacobian,
    geometryRuntime_sourceCertificate.2.volumePositive, geometryRuntime_sourceCertificate.2.volumeFinite⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
