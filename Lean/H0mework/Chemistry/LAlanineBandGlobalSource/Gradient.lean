import H0mework.Chemistry.LAlanineBandGlobalSource.Source
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open SourceGaussianModel ContinuousGradient
open scoped BigOperators NNReal
noncomputable section

def sourceHessianEntryBound (axis direction : Fin 3) : ℝ≥0 :=
  sourceFirstBound (raise zeroJet axis) zeroJet direction +
    sourceFirstBound zeroJet (raise zeroJet axis) direction

def sourceSpeedBound : ℝ≥0 := ∑ axis : Fin 3, sourceFirstBound zeroJet zeroJet axis

def sourceLipschitzBound : ℝ≥0 :=
  ∑ axis : Fin 3, ∑ direction : Fin 3, sourceHessianEntryBound axis direction

theorem sourceHessian_entry_uniform_bound (x : Point) (axis direction : Fin 3) :
    |sourceHessian x axis direction| ≤ (sourceHessianEntryBound axis direction : ℝ) :=
  (abs_add_le _ _).trans (add_le_add
    (source_first_uniform_bound (raise zeroJet axis) zeroJet direction x)
    (source_first_uniform_bound zeroJet (raise zeroJet axis) direction x))

theorem sourceGradient_uniform_bound (x : Point) :
    ‖sourceGradient x‖ ≤ (sourceSpeedBound : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg sourceSpeedBound.coe_nonneg).mpr
  intro axis
  have h := source_first_uniform_bound zeroJet zeroJet axis x
  have hs : sourceFirstBound zeroJet zeroJet axis ≤ sourceSpeedBound :=
    Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ axis)
  exact h.trans (by exact_mod_cast hs)

theorem sourceHessianLinear_uniform_bound (x : Point) :
    ‖sourceHessianLinear x‖ ≤ (sourceLipschitzBound : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ sourceLipschitzBound.coe_nonneg
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg sourceLipschitzBound.coe_nonneg (norm_nonneg v))).mpr
  intro axis
  rw [sourceHessianLinear_apply, Real.norm_eq_abs]
  calc
    |∑ direction : Fin 3, sourceHessian x axis direction * v direction| ≤
        ∑ direction : Fin 3, |sourceHessian x axis direction * v direction| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ direction : Fin 3, (sourceHessianEntryBound axis direction : ℝ) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro direction _
      rw [abs_mul]
      exact mul_le_mul (sourceHessian_entry_uniform_bound x axis direction)
        (norm_le_pi_norm v direction) (abs_nonneg _) (by positivity)
    _ = (∑ direction : Fin 3, (sourceHessianEntryBound axis direction : ℝ)) * ‖v‖ := by
      rw [Finset.sum_mul]
    _ ≤ (sourceLipschitzBound : ℝ) * ‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      have h : (∑ direction : Fin 3, sourceHessianEntryBound axis direction) ≤ sourceLipschitzBound :=
        Finset.single_le_sum (f := fun a : Fin 3 => ∑ d : Fin 3, sourceHessianEntryBound a d)
          (fun _ _ => zero_le) (Finset.mem_univ axis)
      exact_mod_cast h

theorem sourceGradient_globally_lipschitz : LipschitzWith sourceLipschitzBound sourceGradient := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (sourceGradient_hasFDerivAt x).differentiableAt)
  intro x
  rw [(sourceGradient_hasFDerivAt x).fderiv]
  exact_mod_cast sourceHessianLinear_uniform_bound x

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
