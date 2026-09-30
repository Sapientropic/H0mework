import H0mework.Chemistry.LAlanineWholeCell.ReplayModel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceSignedEvaluator WholeCellPartition IntervalParameterMap

theorem q0_inputs0 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 0 0 stage).position axis = WholeCellSource.box (sourceCall 0 0 stage) axis := by
  decide +kernel

theorem q0_inputs1 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 0 1 stage).position axis = WholeCellSource.box (sourceCall 0 1 stage) axis := by
  decide +kernel

theorem q0_inputs2 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 0 2 stage).position axis = WholeCellSource.box (sourceCall 0 2 stage) axis := by
  decide +kernel

theorem q0_inputs3 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 0 3 stage).position axis = WholeCellSource.box (sourceCall 0 3 stage) axis := by
  decide +kernel

theorem q0_target_position : ∀ axis : Fin 3,
    (generatedStates 0 4).position axis = reportedTargetPosition 0 axis := by decide +kernel

theorem q0_target_derivative : ∀ axis direction : Fin 3,
    (generatedStates 0 4).derivative axis direction = reportedTargetJacobian 0 axis direction := by decide +kernel

theorem q0_final_field : ∀ axis : Fin 3,
    (generatedStates 0 4).position axis = WholeCellSource.box (finalField 0) axis := by decide +kernel

theorem q0_target_laplacian : generatedTargetLaplacian 0 = reportedTargetLaplacian 0 := by decide +kernel
theorem q0_target_determinant : generatedTargetDeterminant 0 = reportedTargetDeterminant 0 := by decide +kernel
theorem q0_target_integrand : generatedTargetIntegrand 0 = reportedTargetIntegrand 0 := by decide +kernel
theorem q0_target_integral :
    mul (generatedTargetIntegrand 0) (point (quarterMeasure 0)) = reportedTargetIntegral 0 := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
