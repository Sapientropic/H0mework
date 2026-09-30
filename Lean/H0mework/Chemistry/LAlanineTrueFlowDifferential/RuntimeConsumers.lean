import H0mework.Chemistry.LAlanineTrueFlowDifferential.RuntimeParentConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed TrueFlowDifferential TrueTubeWholeActual
open WholeCellPartition WholeCellBoundary WholeCellBoundary.Geometry Set
noncomputable section

theorem differentialRuntime_source_budget :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    type_of% source_margin_real ∧ type_of% actual_volterra_budget :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.sourceMargin,
    differentialRuntime_sourceCertificate.2.sourceBudget⟩

theorem differentialRuntime_original_paths :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    (∀ p, generatedDifferentialMaterial.rawPaths (ContinuousParameterMap.initialMap 0 4 p.val) =
      actualPath p) ∧ type_of% actualPath_integral_equation :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.originalPath,
    differentialRuntime_sourceCertificate.2.integralEquation⟩

theorem differentialRuntime_initial_response :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    (∀ p, HasStrictFDerivAt generatedDifferentialMaterial.rawPaths
      (generatedDifferentialMaterial.responses p) (ContinuousParameterMap.initialMap 0 4 p.val)) ∧
    (∀ p h, generatedDifferentialMaterial.responses p h = pathConst h +
      volterra (pathHessian p (generatedDifferentialMaterial.responses p h))) ∧
    (∀ p h, generatedDifferentialMaterial.responses p h zeroTime = h) :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.strictInitialDerivative,
    differentialRuntime_sourceCertificate.2.initialResponse, differentialRuntime_sourceCertificate.2.initialValue⟩

theorem differentialRuntime_actual_variational :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    (∀ p h s, HasDerivWithinAt (extendPath (generatedDifferentialMaterial.responses p h))
      (sourceHessianLinear (actualPath p s) (generatedDifferentialMaterial.responses p h s))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ)) ∧
    (∀ p s, HasStrictFDerivAt (fun x => generatedDifferentialMaterial.rawPaths x s)
      (generatedDifferentialMaterial.initialDerivatives p s)
      (ContinuousParameterMap.initialMap 0 4 p.val)) ∧
    (∀ p, generatedDifferentialMaterial.initialDerivatives p zeroTime = ContinuousLinearMap.id ℝ Space) :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.actualVariational,
    differentialRuntime_sourceCertificate.2.fixedTimeDerivative,
    differentialRuntime_sourceCertificate.2.zeroTimeIdentity⟩

theorem differentialRuntime_parameter_derivative :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    (∀ p, generatedDifferentialMaterial.parameterMap p.val =
      generatedDifferentialMaterial.parent.wholeFlows p (p.val 2)) ∧
    (∀ p, HasFDerivWithinAt generatedDifferentialMaterial.parameterMap
      (generatedDifferentialMaterial.jacobians p) fullDomain p.val) ∧
    (∀ p, generatedDifferentialMaterial.jacobians p (Pi.single 2 1) =
      sourceGradient (generatedDifferentialMaterial.parameterMap p.val)) :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.parameterOccurrence,
    differentialRuntime_sourceCertificate.2.parameterDerivative,
    differentialRuntime_sourceCertificate.2.timeColumn⟩

theorem differentialRuntime_seed_columns :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    (∀ p j, j ≠ 2 → generatedDifferentialMaterial.jacobians p (Pi.single j 1) =
      generatedDifferentialMaterial.initialDerivatives p (actualParameterTime p)
        (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val (Pi.single j 1))) ∧
    (∀ p h, generatedDifferentialMaterial.jacobians p h =
      generatedDifferentialMaterial.initialDerivatives p (actualParameterTime p)
        (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val h) +
      h 2 • sourceGradient (generatedDifferentialMaterial.parameterMap p.val)) :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.seedColumns,
    differentialRuntime_sourceCertificate.2.decomposition⟩

theorem differentialRuntime_actual_faces :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    (∀ face p inside, HasFDerivWithinAt (generatedDifferentialMaterial.faceMaps face)
      (generatedDifferentialMaterial.faceDerivatives face p inside) (faceDomain face.1) p) ∧
    (∀ face p inside k, generatedDifferentialMaterial.faceTangents face p inside k =
      generatedDifferentialMaterial.jacobians (trueFaceParameter face p inside)
        (Pi.single (face.1.succAbove k) 1)) :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.faceDerivative,
    differentialRuntime_sourceCertificate.2.faceTangents⟩

theorem differentialRuntime_actual_side_flux :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    (∀ face p inside, face.1 ≠ 2 → generatedDifferentialMaterial.faceTangents face p inside 1 =
      sourceGradient (generatedDifferentialMaterial.faceMaps face p)) ∧
    (∀ face p inside, face.1 ≠ 2 → generatedDifferentialMaterial.faceFluxes face p inside = 0) :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.sideTangent,
    differentialRuntime_sourceCertificate.2.sideFlux⟩

theorem differentialRuntime_nontrivial :
    type_of% (differentialRuntimeFace_factorizes differentialRuntimeSeed (.component .certificate)) ∧
    Set.Nonempty fullDomain ∧ (∀ p, generatedDifferentialMaterial.responses p ≠ 0) ∧
    (∀ p, p.val 2 = 0 → 0 < generatedDifferentialMaterial.jacobians p (Pi.single 2 1) 2) ∧
    (∀ p, p.val 2 = 0 → generatedDifferentialMaterial.jacobians p ≠ 0) :=
  ⟨differentialRuntime_sourceCertificate.1, differentialRuntime_sourceCertificate.2.nonemptyParameters,
    differentialRuntime_sourceCertificate.2.nonzeroResponse,
    differentialRuntime_sourceCertificate.2.positiveTimeColumn,
    differentialRuntime_sourceCertificate.2.nonzeroJacobian⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
