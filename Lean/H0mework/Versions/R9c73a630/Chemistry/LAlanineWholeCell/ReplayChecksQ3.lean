import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.ReplayModel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceSignedEvaluator WholeCellPartition IntervalParameterMap

theorem q3_inputs0 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 3 0 stage).position axis = WholeCellSource.box (sourceCall 3 0 stage) axis := by
  decide +kernel

theorem q3_inputs1 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 3 1 stage).position axis = WholeCellSource.box (sourceCall 3 1 stage) axis := by
  decide +kernel

theorem q3_inputs2 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 3 2 stage).position axis = WholeCellSource.box (sourceCall 3 2 stage) axis := by
  decide +kernel

theorem q3_inputs3 : ∀ stage : Fin 4, ∀ axis : Fin 3,
    (generatedStageInput 3 3 stage).position axis = WholeCellSource.box (sourceCall 3 3 stage) axis := by
  decide +kernel

theorem q3_target_position : ∀ axis : Fin 3,
    (generatedStates 3 4).position axis = reportedTargetPosition 3 axis := by decide +kernel

theorem q3_target_derivative : ∀ axis direction : Fin 3,
    (generatedStates 3 4).derivative axis direction = reportedTargetJacobian 3 axis direction := by decide +kernel

theorem q3_final_field : ∀ axis : Fin 3,
    (generatedStates 3 4).position axis = WholeCellSource.box (finalField 3) axis := by decide +kernel

theorem q3_target_laplacian : generatedTargetLaplacian 3 = reportedTargetLaplacian 3 := by decide +kernel
theorem q3_target_determinant : generatedTargetDeterminant 3 = reportedTargetDeterminant 3 := by decide +kernel
theorem q3_target_integrand : generatedTargetIntegrand 3 = reportedTargetIntegrand 3 := by decide +kernel
theorem q3_target_integral :
    mul (generatedTargetIntegrand 3) (point (quarterMeasure 3)) = reportedTargetIntegral 3 := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
