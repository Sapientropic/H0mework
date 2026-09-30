import H0mework.Chemistry.LAlanineContinuousSource.ChartData
import H0mework.Chemistry.LAlanineContinuousSource.RK4Readout
import H0mework.Chemistry.LAlanineParametric.Injectivity

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceChart

open SourceGaussianModel SourceSignedEvaluator SourceRK4Replay SourceCellGeometry IntervalParameterMap
open ContinuousChart ContinuousParameterMap Set
open scoped BigOperators

noncomputable section

def scaledDomain : Set Point := inputScale ⁻¹' cellDomain
def scaledMap (p : Point) : Point := outputScale (parameterMap 0 4 (inputScale p))
def scaledDerivative (p : Point) : Point →L[ℝ] Point :=
  outputScale.comp ((parameterJacobian 0 4 (inputScale p)).comp inputScale)
def unscale (p : Point) : Point := fun i => p i / (weights i : ℝ)

theorem inputScale_apply (p : Point) (i : Fin 3) : inputScale p i = (weights i : ℝ) * p i := by
  rw [inputScale, matrixLinear_apply, Finset.sum_eq_single i]
  · simp only [weightsMatrix, ite_true]
  · intro j _ hji
    simp only [weightsMatrix, if_neg (Ne.symm hji), Rat.cast_zero, zero_mul]
  · simp

theorem inputScale_unscale (p : Point) : inputScale (unscale p) = p := by
  funext i
  rw [inputScale_apply, unscale]
  have hn : (weights i : ℝ) ≠ 0 := by fin_cases i <;> norm_num [weights]
  exact mul_div_cancel₀ (p i) hn

theorem scaledDomain_convex : Convex ℝ scaledDomain :=
  (convex_Icc (𝕜 := ℝ) _ _).linear_preimage inputScale.toLinearMap

theorem scaledMap_hasFDerivAt (p : Point) : HasFDerivAt scaledMap (scaledDerivative p) p :=
  outputScale.hasFDerivAt.comp p ((parameterMap_hasFDerivAt 0 4 (inputScale p)).comp p inputScale.hasFDerivAt)

attribute [local irreducible] parameterJacobian in
theorem scaled_error_contains (fields : SourceFieldLaw) (p : Point) (inside : p ∈ scaledDomain) :
    MatrixHolds errorBox (scaledDerivative p - ContinuousLinearMap.id ℝ Point) := by
  have target : MatrixHolds reportedTargetJacobian (parameterJacobian 0 4 (inputScale p)) := by
    intro i j
    rw [← target_derivative_recomputed i j]
    exact (generated_target_contains fields (inputScale p) inside).2 i j
  change MatrixHolds errorBox
    ((outputScale.comp (parameterJacobian 0 4 (inputScale p))).comp inputScale - ContinuousLinearMap.id ℝ Point)
  exact subtract_identity_contains _ _
    (matrixMultiply_contains _ _ _ _
      (matrixMultiply_contains _ _ _ _ (matrixLinear_contains preconditioner) target)
      (matrixLinear_contains weightsMatrix))

theorem scaled_derivative_bound (fields : SourceFieldLaw) (p : Point) (inside : p ∈ scaledDomain) :
    ‖scaledDerivative p - ContinuousLinearMap.id ℝ Point‖ ≤ (1 / 2 : ℝ) := by
  have h := matrix_norm_le errorBox _ (1 / 2) (by norm_num)
    (scaled_error_contains fields p inside) error_rows_small
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem scaledMap_injOn (fields : SourceFieldLaw) : InjOn scaledMap scaledDomain :=
  injOn_of_derivative_near_identity scaledMap scaledDerivative scaledDomain scaledDomain_convex
    (1 / 2) (by norm_num) (fun p _ => scaledMap_hasFDerivAt p) (scaled_derivative_bound fields)

theorem actual_chart_injOn (fields : SourceFieldLaw) : InjOn (parameterMap 0 4) cellDomain := by
  intro p hp q hq same
  have hp' : unscale p ∈ scaledDomain := by
    change inputScale (unscale p) ∈ cellDomain
    rwa [inputScale_unscale]
  have hq' : unscale q ∈ scaledDomain := by
    change inputScale (unscale q) ∈ cellDomain
    rwa [inputScale_unscale]
  have h : scaledMap (unscale p) = scaledMap (unscale q) := by
    simp only [scaledMap, inputScale_unscale, same]
  have equality := congrArg inputScale (scaledMap_injOn fields hp' hq' h)
  simpa only [inputScale_unscale] using equality

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceChart
