import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlow.RuntimeParentConsumers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime

open SourceGaussianModel SourceSignedEvaluator WholeBandSource WholeBandReplay WholeBandActual Set
noncomputable section

theorem wholeBandFlowRuntime_arithmetic :
    type_of% (wholeBandFlowRuntimeFace_factorizes wholeBandFlowRuntimeSeed (.component .certificate)) ∧
    (∀ c d i, InputArithmetic (generatedWholeBandFlowMaterial.rows c d i) i) ∧
    type_of% endpoint_next_initial ∧ type_of% common_initial ∧ type_of% time_step ∧
    type_of% time_next_start ∧ type_of% time_endpoints :=
  ⟨wholeBandFlowRuntime_sourceCertificate.1, wholeBandFlowRuntime_sourceCertificate.2.arithmetic,
    wholeBandFlowRuntime_sourceCertificate.2.adjacency, wholeBandFlowRuntime_sourceCertificate.2.commonInitial,
    wholeBandFlowRuntime_sourceCertificate.2.timeStep, wholeBandFlowRuntime_sourceCertificate.2.timeNext,
    wholeBandFlowRuntime_sourceCertificate.2.timeEnds⟩

theorem wholeBandFlowRuntime_seed_and_actual_generation :
    type_of% (wholeBandFlowRuntimeFace_factorizes wholeBandFlowRuntimeSeed (.component .certificate)) ∧
    (∀ c p, p ∈ generatedWholeBandFlowMaterial.parent.cellDomains c →
      InRectangle (generatedWholeBandFlowMaterial.parent.initialBoxes c 0 0)
        (generatedWholeBandFlowMaterial.parent.cellSeeds c p)) ∧
    type_of% first_initial_field ∧ type_of% first_tube_field ∧ type_of% source_first_step ∧
    type_of% source_cell0_first_curves ∧ type_of% source_cell0_first_reenters :=
  ⟨wholeBandFlowRuntime_sourceCertificate.1, wholeBandFlowRuntime_sourceCertificate.2.seeds,
    wholeBandFlowRuntime_sourceCertificate.2.initialFields, wholeBandFlowRuntime_sourceCertificate.2.tubeFields,
    wholeBandFlowRuntime_sourceCertificate.2.localStep, wholeBandFlowRuntime_sourceCertificate.2.actualFirstCurves,
    wholeBandFlowRuntime_sourceCertificate.2.reentry⟩

theorem wholeBandFlowRuntime_actual_targets :
    type_of% (wholeBandFlowRuntimeFace_factorizes wholeBandFlowRuntimeSeed (.component .certificate)) ∧
    (∀ d initial, generatedWholeBandFlowMaterial.curves d initial 0 = initial.val ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt (generatedWholeBandFlowMaterial.curves d initial)
          (TrueTubeTrace.signedGradient (sign d) (generatedWholeBandFlowMaterial.curves d initial t))
          (Icc 0 (stepSize : ℝ)) t ∧
        InRectangle (tubeBox 0 d 0) (generatedWholeBandFlowMaterial.curves d initial t)) ∧
      InRectangle (endpointBox 0 d 0) (generatedWholeBandFlowMaterial.curves d initial stepSize)) ∧
    (∀ d initial, (generatedWholeBandFlowMaterial.targets d initial).val =
      generatedWholeBandFlowMaterial.curves d initial stepSize) ∧
    (∀ d initial, InRectangle (initialBox 0 d 1) (generatedWholeBandFlowMaterial.targets d initial).val ∧
      InputArithmetic (generatedWholeBandFlowMaterial.rows 0 d 1) 1) ∧
    type_of% firstCurve_continuousOn ∧ type_of% firstCurve_stays_in_sourceCube :=
  ⟨wholeBandFlowRuntime_sourceCertificate.1, wholeBandFlowRuntime_sourceCertificate.2.curveSpec,
    wholeBandFlowRuntime_sourceCertificate.2.targetGenerated, wholeBandFlowRuntime_sourceCertificate.2.targetNextArithmetic,
    wholeBandFlowRuntime_sourceCertificate.2.continuous, wholeBandFlowRuntime_sourceCertificate.2.sourceCube⟩

theorem wholeBandFlowRuntime_common_source_flow :
    type_of% (wholeBandFlowRuntimeFace_factorizes wholeBandFlowRuntimeSeed (.component .certificate)) ∧
    (∀ p, generatedWholeBandFlowMaterial.fullFirstFlows p 0 = generatedWholeBandFlowMaterial.parent.cellSeeds 0 p.val) ∧
    (∀ p, IsIntegralCurveOn (generatedWholeBandFlowMaterial.fullFirstFlows p)
      (fun _ => ContinuousGradient.sourceGradient) firstWindow) ∧
    type_of% fullFlow_stays ∧ type_of% fullFlow_zero_derivative ∧ type_of% firstCurve_eq_sourceWindow ∧
    (∀ p, EqOn (generatedWholeBandFlowMaterial.fullFirstFlows p)
      (generatedWholeBandFlowMaterial.originalFlowKernel (generatedWholeBandFlowMaterial.parent.cellSeeds 0 p.val)) firstWindow) ∧
    type_of% sourceRaw_original_on_firstWindow :=
  ⟨wholeBandFlowRuntime_sourceCertificate.1, wholeBandFlowRuntime_sourceCertificate.2.fullStarts,
    wholeBandFlowRuntime_sourceCertificate.2.fullOriginal, wholeBandFlowRuntime_sourceCertificate.2.fullStays,
    wholeBandFlowRuntime_sourceCertificate.2.zeroDerivative, wholeBandFlowRuntime_sourceCertificate.2.canonicalLocal,
    wholeBandFlowRuntime_sourceCertificate.2.canonicalFull, wholeBandFlowRuntime_sourceCertificate.2.canonicalOriginal⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandFlowRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
