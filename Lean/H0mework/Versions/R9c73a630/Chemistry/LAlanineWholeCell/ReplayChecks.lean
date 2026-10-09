import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.ReplayChecksQ0
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.ReplayChecksQ1
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.ReplayChecksQ2
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.ReplayChecksQ3

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceSignedEvaluator WholeCellPartition IntervalParameterMap

theorem every_source_input (q : Quarter) (step stage : Fin 4) :
    (generatedStageInput q step stage).position = WholeCellSource.box (sourceCall q step stage) := by
  funext axis
  fin_cases q <;> fin_cases step
  · exact q0_inputs0 stage axis
  · exact q0_inputs1 stage axis
  · exact q0_inputs2 stage axis
  · exact q0_inputs3 stage axis
  · exact q1_inputs0 stage axis
  · exact q1_inputs1 stage axis
  · exact q1_inputs2 stage axis
  · exact q1_inputs3 stage axis
  · exact q2_inputs0 stage axis
  · exact q2_inputs1 stage axis
  · exact q2_inputs2 stage axis
  · exact q2_inputs3 stage axis
  · exact q3_inputs0 stage axis
  · exact q3_inputs1 stage axis
  · exact q3_inputs2 stage axis
  · exact q3_inputs3 stage axis

theorem target_position_recomputed (q : Quarter) : ∀ axis : Fin 3, (generatedStates q 4).position axis = reportedTargetPosition q axis := by
  intro axis
  fin_cases q
  · exact q0_target_position axis
  · exact q1_target_position axis
  · exact q2_target_position axis
  · exact q3_target_position axis

theorem target_derivative_recomputed (q : Quarter) : ∀ axis direction : Fin 3, (generatedStates q 4).derivative axis direction = reportedTargetJacobian q axis direction := by
  intro axis direction
  fin_cases q
  · exact q0_target_derivative axis direction
  · exact q1_target_derivative axis direction
  · exact q2_target_derivative axis direction
  · exact q3_target_derivative axis direction

theorem final_field_is_generated_target (q : Quarter) : ∀ axis : Fin 3, (generatedStates q 4).position axis = WholeCellSource.box (finalField q) axis := by
  intro axis
  fin_cases q
  · exact q0_final_field axis
  · exact q1_final_field axis
  · exact q2_final_field axis
  · exact q3_final_field axis

theorem target_laplacian_recomputed (q : Quarter) : generatedTargetLaplacian q = reportedTargetLaplacian q := by
  fin_cases q
  · exact q0_target_laplacian
  · exact q1_target_laplacian
  · exact q2_target_laplacian
  · exact q3_target_laplacian

theorem target_determinant_recomputed (q : Quarter) : generatedTargetDeterminant q = reportedTargetDeterminant q := by
  fin_cases q
  · exact q0_target_determinant
  · exact q1_target_determinant
  · exact q2_target_determinant
  · exact q3_target_determinant

theorem target_integrand_recomputed (q : Quarter) : generatedTargetIntegrand q = reportedTargetIntegrand q := by
  fin_cases q
  · exact q0_target_integrand
  · exact q1_target_integrand
  · exact q2_target_integrand
  · exact q3_target_integrand

theorem target_integral_recomputed (q : Quarter) : mul (generatedTargetIntegrand q) (point (quarterMeasure q)) = reportedTargetIntegral q := by
  fin_cases q
  · exact q0_target_integral
  · exact q1_target_integral
  · exact q2_target_integral
  · exact q3_target_integral

def hullPair (a b : Pair) : Pair := (min a.1 b.1, max a.2 b.2)
noncomputable def sourceHull (i j : Fin 3) : Pair :=
  hullPair (hullPair (reportedTargetJacobian 0 i j) (reportedTargetJacobian 1 i j))
    (hullPair (reportedTargetJacobian 2 i j) (reportedTargetJacobian 3 i j))

theorem common_hull_recomputed : ∀ i j : Fin 3, commonJacobian i j = sourceHull i j := by decide +kernel
theorem quarter_inside_common_hull : ∀ q : Quarter, ∀ i j : Fin 3,
    (commonJacobian i j).1 ≤ (reportedTargetJacobian q i j).1 ∧
      (reportedTargetJacobian q i j).2 ≤ (commonJacobian i j).2 := by decide +kernel

theorem determinant_positive : ∀ q : Quarter, 0 < (reportedTargetDeterminant q).1 := by decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
