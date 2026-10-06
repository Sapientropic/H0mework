import H0mework.Realization.Perfectification.Quantum.Forms.Bounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! The existing C* norm-spectrum theorem and bounded inverse criterion
produce approximate norm eigenvectors without compactness. -/

set_option autoImplicit false

namespace SaturationMonoid.Quantum.Forms.Approximate

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem small_unit (T : H →L[ℂ] H) (symmetric : IsSelfAdjoint T) (notUnit : ¬IsUnit T)
    (ε : ℝ) (positive : 0 < ε) : ∃ x : H, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  by_contra! lower
  have bound (x : H) : ‖x‖ ≤ ε⁻¹ * ‖T x‖ := by
    by_cases zero : x = 0
    · simp [zero]
    have normalized := lower ((‖x‖ : ℂ)⁻¹ • x) (norm_smul_inv_norm zero)
    have scaled : ε ≤ ‖T x‖ / ‖x‖ := by
      simpa only [map_smul, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg x), div_eq_mul_inv, mul_comm] using normalized
    rw [inv_mul_eq_div, le_div_iff₀ positive]
    exact (mul_comm _ _).trans_le ((le_div_iff₀ (norm_pos_iff.mpr zero)).mp scaled)
  have anti : AntilipschitzWith ⟨ε⁻¹, inv_nonneg.mpr positive.le⟩ T := T.antilipschitz_of_bound bound
  have dense := Transfer.Polar.selfAdjoint_denseRange T symmetric anti.injective
  have closed := anti.isClosed_range T.uniformContinuous
  have onto : Function.Surjective T := by
    intro x
    have member := dense x
    rw [closed.closure_eq] at member
    exact member
  exact notUnit (ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨anti.injective, onto⟩)

variable [Nontrivial H]

omit [CompleteSpace H] in
theorem norm_positive (R : H →L[ℂ] H) (injective : Function.Injective R) : 0 < ‖R‖ := by
  apply norm_pos_iff.mpr
  intro zero
  obtain ⟨x, nonzero⟩ := exists_ne (0 : H)
  apply nonzero
  apply injective
  simp [zero]

theorem norm_approximate (R : H →L[ℂ] H) (positive : R.IsPositive)
    (ε : ℝ) (epsilon : 0 < ε) :
    ∃ x : H, ‖x‖ = 1 ∧ ‖R x - (‖R‖ : ℂ) • x‖ < ε := by
  have spectral : ‖R‖ ∈ spectrum ℝ R := CStarAlgebra.norm_mem_spectrum_of_nonneg
    ((ContinuousLinearMap.nonneg_iff_isPositive R).mpr positive)
  have complexSpectral : (‖R‖ : ℂ) ∈ spectrum ℂ R := spectrum.algebraMap_mem ℂ spectral
  let T : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) (‖R‖ : ℂ) - R
  have symmetric : IsSelfAdjoint T :=
    (((IsSelfAdjoint.all ‖R‖).algebraMap ℂ).algebraMap _).sub positive.isSelfAdjoint
  obtain ⟨x, unit, small⟩ := small_unit T symmetric (spectrum.mem_iff.mp complexSpectral) ε epsilon
  refine ⟨x, unit, ?_⟩
  have small' : ‖(‖R‖ : ℂ) • x - R x‖ < ε := by
    simpa only [T, sub_apply, ContinuousLinearMap.algebraMap_apply] using small
  exact (norm_sub_rev _ _).trans_lt small'

end
end SaturationMonoid.Quantum.Forms.Approximate
