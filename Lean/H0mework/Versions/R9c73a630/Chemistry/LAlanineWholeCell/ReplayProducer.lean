import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.ReplayInjectivity

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceGaussianModel SourceSignedEvaluator WholeCellPartition ContinuousParameterMap IntervalParameterMap

theorem sourceReplayEquations :
    type_of% quarter_source_bounds ∧ type_of% initial_position_reused ∧ type_of% initial_derivative_reused ∧
    type_of% step_size_recomputed ∧ type_of% step_derivative_reused ∧ type_of% every_source_input ∧
    type_of% target_position_recomputed ∧ type_of% target_derivative_recomputed ∧
    type_of% final_field_is_generated_target ∧ type_of% target_laplacian_recomputed ∧
    type_of% target_determinant_recomputed ∧ type_of% target_integrand_recomputed ∧
    type_of% target_integral_recomputed ∧ type_of% common_hull_recomputed ∧
    type_of% source_conditioning_calculated :=
  ⟨quarter_source_bounds, initial_position_reused, initial_derivative_reused, step_size_recomputed,
    step_derivative_reused, every_source_input, target_position_recomputed, target_derivative_recomputed,
    final_field_is_generated_target, target_laplacian_recomputed, target_determinant_recomputed,
    target_integrand_recomputed, target_integral_recomputed, common_hull_recomputed, source_conditioning_calculated⟩

/-- The only semantic input is the registered source Gaussian field family, not a trajectory or no-fold verdict. -/
theorem wholeCellFromSourceFields (fields : SourceFieldLaw) :
    type_of% sourceReplayEquations ∧
    (∀ q p, p ∈ quarterDomain q → JetHolds (generatedStates q 4) (parameterMap 0 4 p) (parameterJacobian 0 4 p)) ∧
    (∀ p ∈ fullDomain, MatrixHolds commonJacobian (parameterJacobian 0 4 p)) ∧
    (∀ p ∈ fullDomain, 0 < (jacobianMatrix 0 4 p).det) ∧
    Set.InjOn (parameterMap 0 4) fullDomain ∧
    (∀ q, Holds (integralPair (generatedTargetIntegrand q) (quarterLowerQ q) (quarterUpperQ q))
      (∫ p in quarterDomain q, signedLaplacian 0 4 p)) ∧
    fullDomain.Nonempty :=
  ⟨sourceReplayEquations, generated_target_contains fields, common_jacobian_contains fields,
    full_jacobian_positive fields, actual_chart_injOn fields, quarter_integral_from_source_fields fields, full_nonempty⟩

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
