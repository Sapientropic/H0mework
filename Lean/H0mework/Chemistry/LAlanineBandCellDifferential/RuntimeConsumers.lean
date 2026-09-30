import H0mework.Chemistry.LAlanineBandCellDifferential.RuntimeParentConsumers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandGeometry WholeBandActual TrueFlowDifferential
open WholeBandCell0Differential Set
noncomputable section

theorem wholeBandCell0DifferentialRuntime_source :
    type_of% (wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0DifferentialRuntimeSeed (.component .certificate)) ∧
    (∀ d i, AnalyticBounds (generatedWholeBandCell0DifferentialMaterial.parent.parent.rows 0 d i)) ∧
    (∀ p (t : Time), ‖sourceHessianLinear (generatedWholeBandCell0DifferentialMaterial.parent.fullFlows p t.val)‖ ≤ (17/20 : ℝ)) ∧
    type_of% path_near_cell0_in_cube ∧
    type_of% cell0_pathHessian_norm ∧
    type_of% cell0_volterraHessian_norm_lt_one ∧
    type_of% cell0_rawPath_integral_equation ∧
    (∀ p, HasStrictFDerivAt rawPath (generatedWholeBandCell0DifferentialMaterial.responses p) (cellSeed 0 p.val)) :=
  ⟨wholeBandCell0DifferentialRuntime_sourceCertificate.1,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.analyticBounds,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.actualHessian,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.nearbyCube,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.pathHessian,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.volterraContractive,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.originalIntegral,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.initialResponse⟩

theorem wholeBandCell0DifferentialRuntime_variational :
    type_of% (wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0DifferentialRuntimeSeed (.component .certificate)) ∧
    (∀ p h, generatedWholeBandCell0DifferentialMaterial.responses p h = pathConst h +
      volterra (cell0_pathHessian p (generatedWholeBandCell0DifferentialMaterial.responses p h))) ∧
    type_of% cell0_responseCurve_is_actual ∧
    type_of% cell0_sourceResponse_variational ∧
    type_of% cell0_initialFlowDerivative_variational ∧
    (∀ p s, HasStrictFDerivAt (fun x => rawPath x s) (generatedWholeBandCell0DifferentialMaterial.initialDerivatives p s) (cellSeed 0 p.val)) ∧
    (∀ p, generatedWholeBandCell0DifferentialMaterial.initialDerivatives p zeroTime = ContinuousLinearMap.id ℝ Space) ∧
    (∀ p s, Function.Injective (generatedWholeBandCell0DifferentialMaterial.initialDerivatives p s)) ∧
    (∀ p s, generatedWholeBandCell0DifferentialMaterial.initialDerivatives p s (sourceGradient (cellSeed 0 p.val)) =
      sourceGradient (rawPath (cellSeed 0 p.val) s)) :=
  ⟨wholeBandCell0DifferentialRuntime_sourceCertificate.1,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.responseIntegral,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.primitiveRecognition,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.responseVariational,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.actualVariational,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.initialDerivative,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.initialIdentity,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.responseInjective,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.gradientTransport⟩

theorem wholeBandCell0DifferentialRuntime_scaled :
    type_of% (wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0DifferentialRuntimeSeed (.component .certificate)) ∧
    (∀ p t, generatedWholeBandCell0DifferentialMaterial.scaledPaths p t = rawPath (cellSeed 0 p.val)
      (scaledTime (cell0_scaleAt p) (cell0_scaleAt_abs_le_one p) t)) ∧
    (∀ p, generatedWholeBandCell0DifferentialMaterial.scaledPaths p = pathConst (cellSeed 0 p.val) +
      cell0_scaleAt p • volterra (pathGradient (generatedWholeBandCell0DifferentialMaterial.scaledPaths p))) ∧
    type_of% cell0_scaledVolterra_norm_bound ∧
    (∀ p, HasStrictFDerivAt (cell0_scaledSolution p) (generatedWholeBandCell0DifferentialMaterial.scaledResponses p) (cell0_sourceInput p)) ∧
    type_of% cell0_scaledSolution_eq_rawPath ∧
    (∀ q, HasFDerivAt generatedWholeBandCell0DifferentialMaterial.parameterInputs (cell0_parameterInputDerivative q) q) ∧
    (∀ q, q ∈ cellDomain 0 →
      scaledRawPath (generatedWholeBandCell0DifferentialMaterial.parameterInputs q).1 (generatedWholeBandCell0DifferentialMaterial.parameterInputs q).2 endpointTime =
        generatedWholeBandCell0DifferentialMaterial.parent.parameterMap q) ∧
    (∀ p, HasFDerivWithinAt generatedWholeBandCell0DifferentialMaterial.parent.parameterMap
      (generatedWholeBandCell0DifferentialMaterial.jacobians p) (cellDomain 0) p.val) :=
  ⟨wholeBandCell0DifferentialRuntime_sourceCertificate.1,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.scaledPath,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.scaledIntegral,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.scaledBound,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.scaledResponse,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.scaledRecognition,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.parameterInput,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.endpointRecognition,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.actualParameterDerivative⟩

theorem wholeBandCell0DifferentialRuntime_columns :
    type_of% (wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0DifferentialRuntimeSeed (.component .certificate)) ∧
    type_of% cell0_domain_eq_Icc ∧
    type_of% cell0_axis_strict ∧
    type_of% cell0_domain_uniqueDiffOn ∧
    type_of% cell0_seed_width_positive ∧
    (∀ p, Function.Injective (generatedWholeBandCell0DifferentialMaterial.seedFrames p)) ∧
    (∀ p, generatedWholeBandCell0DifferentialMaterial.jacobians p (Pi.single 2 1) = sourceGradient (generatedWholeBandCell0DifferentialMaterial.parent.parameterMap p.val)) ∧
    (∀ p j, j ≠ 2 → generatedWholeBandCell0DifferentialMaterial.jacobians p (Pi.single j 1) =
      generatedWholeBandCell0DifferentialMaterial.initialDerivatives p (cell0_actualParameterTime p)
        (bandSeedDerivative 0 (Geometry.Source.epsilon 0) p.val (Pi.single j 1))) ∧
    (∀ p h, generatedWholeBandCell0DifferentialMaterial.jacobians p h =
      generatedWholeBandCell0DifferentialMaterial.initialDerivatives p (cell0_actualParameterTime p)
        (bandSeedDerivative 0 (Geometry.Source.epsilon 0) p.val h) +
      h 2 • sourceGradient (generatedWholeBandCell0DifferentialMaterial.parent.parameterMap p.val)) :=
  ⟨wholeBandCell0DifferentialRuntime_sourceCertificate.1,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.domainRectangle,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.domainWidths,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.domainUnique,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.seedWidth,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.seedInjective,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.timeColumn,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.seedColumns,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.decomposition⟩

theorem wholeBandCell0DifferentialRuntime_nondegenerate :
    type_of% (wholeBandCell0DifferentialRuntimeFace_factorizes wholeBandCell0DifferentialRuntimeSeed (.component .certificate)) ∧
    (∀ p, generatedWholeBandCell0DifferentialMaterial.jacobians p =
      (generatedWholeBandCell0DifferentialMaterial.initialDerivatives p (cell0_actualParameterTime p)).comp (generatedWholeBandCell0DifferentialMaterial.seedFrames p)) ∧
    (∀ p, Function.Injective (generatedWholeBandCell0DifferentialMaterial.jacobians p)) ∧
    (∀ p, LinearMap.det (generatedWholeBandCell0DifferentialMaterial.jacobians p).toLinearMap ≠ 0) ∧
    (∀ p s, (generatedWholeBandCell0DifferentialMaterial.responseEquivalences p s : Point →L[ℝ] Point) = generatedWholeBandCell0DifferentialMaterial.initialDerivatives p s) ∧
    (∀ p, (generatedWholeBandCell0DifferentialMaterial.jacobianEquivalences p : Point →L[ℝ] Point) = generatedWholeBandCell0DifferentialMaterial.jacobians p) ∧
    (∀ p, generatedWholeBandCell0DifferentialMaterial.jacobians p = fderivWithin ℝ generatedWholeBandCell0DifferentialMaterial.parent.parameterMap (cellDomain 0) p.val) :=
  ⟨wholeBandCell0DifferentialRuntime_sourceCertificate.1,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.factorization,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.jacobianInjective,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.determinant,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.responseEquivRecognition,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.jacobianEquivRecognition,
    wholeBandCell0DifferentialRuntime_sourceCertificate.2.canonicalDerivative⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
