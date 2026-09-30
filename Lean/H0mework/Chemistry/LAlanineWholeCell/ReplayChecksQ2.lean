import H0mework.Chemistry.LAlanineWholeCell.ReplayModel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceSignedEvaluator WholeCellPartition IntervalParameterMap

theorem q2_inputs0 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 2 0 stage).position axis = WholeCellSource.box (sourceCall 2 0 stage) axis := by
  decide +kernel

theorem q2_inputs1 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 2 1 stage).position axis = WholeCellSource.box (sourceCall 2 1 stage) axis := by
  decide +kernel

theorem q2_inputs2 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 2 2 stage).position axis = WholeCellSource.box (sourceCall 2 2 stage) axis := by
  decide +kernel

theorem q2_inputs3 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 2 3 stage).position axis = WholeCellSource.box (sourceCall 2 3 stage) axis := by
  decide +kernel

theorem q2_target_position : ∀ axis : Fin 3,
    (generatedStates 2 4).position axis = reportedTargetPosition 2 axis := by decide +kernel

theorem q2_target_derivative : ∀ axis direction : Fin 3,
    (generatedStates 2 4).derivative axis direction = reportedTargetJacobian 2 axis direction := by decide +kernel

theorem q2_final_field : ∀ axis : Fin 3,
    (generatedStates 2 4).position axis = WholeCellSource.box (finalField 2) axis := by decide +kernel

theorem q2_target_laplacian : generatedTargetLaplacian 2 = reportedTargetLaplacian 2 := by decide +kernel
theorem q2_target_determinant : generatedTargetDeterminant 2 = reportedTargetDeterminant 2 := by decide +kernel
theorem q2_target_integrand : generatedTargetIntegrand 2 = reportedTargetIntegrand 2 := by decide +kernel
theorem q2_target_integral :
    mul (generatedTargetIntegrand 2) (point (quarterMeasure 2)) = reportedTargetIntegral 2 := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
