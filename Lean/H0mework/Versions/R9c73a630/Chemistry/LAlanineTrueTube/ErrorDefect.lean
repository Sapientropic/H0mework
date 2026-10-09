import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.MatrixAllFields
import H0mework.Versions.AB.Chemistry.LAlanineParametric.MatrixBounds

/-! The actual finite map supplies its own ODE defect through its true parameter derivative. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeError

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap ContinuousChart
open WholeCellPartition WholeCellReplay ContinuousGradient ContinuousParameterMap
open scoped BigOperators
noncomputable section

def defectPair (q : Quarter) (axis : Fin 3) : Pair :=
  sub (reportedTargetJacobian q axis 2) ((recordedField (finalField q)).gradient axis)

def quarterDefectBound (q : Quarter) : ℚ := ∑ axis : Fin 3, magnitude (defectPair q axis)

theorem quarterDefectBound_nonneg (q : Quarter) : 0 ≤ quarterDefectBound q := by
  apply Finset.sum_nonneg
  intro axis _
  exact (abs_nonneg _).trans (le_max_left _ _)

theorem actual_defect_contains (q : Quarter) (p : Point) (inside : p ∈ quarterDomain q) :
    ∀ axis : Fin 3, Holds (defectPair q axis)
      ((parameterJacobian 0 4 p (Pi.single 2 1) - sourceGradient (parameterMap 0 4 p)) axis) := by
  have derivative := (generated_target_contains WholeCellMatrix.all_actual_fields q p inside).2
  have gradient := (WholeCellMatrix.all_actual_fields (finalField q) _
    (generated_target_in_final_field WholeCellMatrix.all_actual_fields q p inside)).1
  intro axis
  have entry := derivative axis 2
  rw [target_derivative_recomputed] at entry
  exact sub_holds _ _ _ _ entry (gradient axis)

theorem actual_defect_norm_le (q : Quarter) (p : Point) (inside : p ∈ quarterDomain q) :
    ‖parameterJacobian 0 4 p (Pi.single 2 1) - sourceGradient (parameterMap 0 4 p)‖ ≤
      (quarterDefectBound q : ℝ) := by
  have nonnegative : (0 : ℝ) ≤ (quarterDefectBound q : ℝ) :=
    Rat.cast_nonneg.mpr (quarterDefectBound_nonneg q)
  apply (pi_norm_le_iff_of_nonneg nonnegative).mpr
  intro axis
  rw [Real.norm_eq_abs]
  refine (magnitude_contains _ _ (actual_defect_contains q p inside axis)).trans ?_
  apply Rat.cast_le.mpr
  change magnitude (defectPair q axis) ≤ ∑ i : Fin 3, magnitude (defectPair q i)
  apply Finset.single_le_sum _ (Finset.mem_univ axis)
  intro i _
  exact (abs_nonneg _).trans (le_max_left _ _)

end
end LAlanine40K2025.BasinRefinement.TrueTubeError
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
