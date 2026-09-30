import H0mework.Chemistry.LAlanineContinuousSource.RK4ReplayData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRK4Replay

open SourceRectangle SourceSignedEvaluator SourceCellGeometry IntervalParameterMap

theorem first_four_inputs : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 0 stage).position axis = actualBox (sourceCall 0 stage) axis := by
  decide +kernel

theorem second_four_inputs : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 1 stage).position axis = actualBox (sourceCall 1 stage) axis := by
  decide +kernel

theorem third_four_inputs : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 2 stage).position axis = actualBox (sourceCall 2 stage) axis := by
  decide +kernel

theorem fourth_four_inputs : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 3 stage).position axis = actualBox (sourceCall 3 stage) axis := by
  decide +kernel

theorem every_source_input (step stage : Fin 4) :
    (generatedStageInput step stage).position = actualBox (sourceCall step stage) := by
  funext axis
  fin_cases step
  · exact first_four_inputs stage axis
  · exact second_four_inputs stage axis
  · exact third_four_inputs stage axis
  · exact fourth_four_inputs stage axis

theorem target_position_recomputed : ∀ axis : Fin 3,
    (generatedStates 4).position axis = reportedTargetPosition axis := by decide +kernel

theorem target_derivative_recomputed : ∀ axis direction : Fin 3,
    (generatedStates 4).derivative axis direction = reportedTargetJacobian axis direction := by decide +kernel

theorem final_field_is_generated_target : ∀ axis : Fin 3,
    (generatedStates 4).position axis = actualBox 16 axis := by decide +kernel

theorem target_laplacian_recomputed : generatedTargetLaplacian = reportedTargetLaplacian := by decide +kernel
theorem target_determinant_recomputed : generatedTargetDeterminant = reportedTargetDeterminant := by decide +kernel
theorem target_integrand_recomputed : generatedTargetIntegrand = reportedTargetIntegrand := by decide +kernel

theorem target_integral_recomputed :
    mul generatedTargetIntegrand (point cellVolume) = reportedTargetIntegral := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRK4Replay
