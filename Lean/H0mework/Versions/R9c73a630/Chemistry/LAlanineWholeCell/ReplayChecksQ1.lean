import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.ReplayModel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceSignedEvaluator WholeCellPartition IntervalParameterMap

theorem q1_inputs0 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 1 0 stage).position axis = WholeCellSource.box (sourceCall 1 0 stage) axis := by
  decide +kernel

theorem q1_inputs1 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 1 1 stage).position axis = WholeCellSource.box (sourceCall 1 1 stage) axis := by
  decide +kernel

theorem q1_inputs2 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 1 2 stage).position axis = WholeCellSource.box (sourceCall 1 2 stage) axis := by
  decide +kernel

theorem q1_inputs3 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 1 3 stage).position axis = WholeCellSource.box (sourceCall 1 3 stage) axis := by
  decide +kernel

theorem q1_target_position : ∀ axis : Fin 3,
    (generatedStates 1 4).position axis = reportedTargetPosition 1 axis := by decide +kernel

theorem q1_target_derivative : ∀ axis direction : Fin 3,
    (generatedStates 1 4).derivative axis direction = reportedTargetJacobian 1 axis direction := by decide +kernel

theorem q1_final_field : ∀ axis : Fin 3,
    (generatedStates 1 4).position axis = WholeCellSource.box (finalField 1) axis := by decide +kernel

theorem q1_target_laplacian : generatedTargetLaplacian 1 = reportedTargetLaplacian 1 := by decide +kernel
theorem q1_target_determinant : generatedTargetDeterminant 1 = reportedTargetDeterminant 1 := by decide +kernel
theorem q1_target_integrand : generatedTargetIntegrand 1 = reportedTargetIntegrand 1 := by decide +kernel
theorem q1_target_integral :
    mul (generatedTargetIntegrand 1) (point (quarterMeasure 1)) = reportedTargetIntegral 1 := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
