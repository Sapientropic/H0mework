import H0mework.Arithmetic.MobiusSource.MobiusReconstruction

/-! The existing divisor inverse recovers every inner-gap source; no outer cutoff. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

def burnolInnerGapForward (source : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ+, (((n : ℕ) : ℂ)⁻¹) * source (x / (n : ℕ))

/-- The existing divisor inverse recovers an inner-gap source without
requiring an outer support cutoff. -/
theorem burnolCenteredMobiusInverse_forward_innerGap (source : ℝ → ℂ)
    (gap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → source x = 0)
    (constant : ℂ) (x : ℝ) :
    burnolCenteredMobiusInverse (fun t => burnolInnerGapForward source t - constant) x =
      source x := by
  have atZero : source 0 = 0 := gap (by norm_num)
  have quarterGap : ∀ {t : ℝ}, |t| ≤ (1 / 4 : ℝ) → source t = source 0 := by
    intro t inside
    rw [gap inside, atZero]
  have forwardZero : burnolInnerGapForward source 0 = 0 := by
    simp only [burnolInnerGapForward, zero_div, atZero, mul_zero, tsum_zero]
  have jointSummable : Summable (burnolCenteredMobiusReconstructionJointTerm source x) :=
    summable_of_hasFiniteSupport
      (burnolCenteredMobiusReconstructionJointTerm_finiteSupport source quarterGap x)
  calc
    _ = ∑' m : ℕ+, ∑' n : ℕ+,
        burnolCenteredMobiusReconstructionJointTerm source x (n, m) := by
      unfold burnolCenteredMobiusInverse
      apply tsum_congr
      intro m
      simp only [forwardZero, zero_sub, sub_neg_eq_add, sub_add_cancel]
      unfold burnolInnerGapForward
      rw [← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro n
      unfold burnolCenteredMobiusReconstructionJointTerm burnolCenteredMobiusSummand
      rw [atZero, sub_zero, div_div, div_div]
      rw [mul_comm (((m : ℕ) : ℝ)) (((n : ℕ) : ℝ))]
      ring
    _ = ∑' n : ℕ+, ∑' m : ℕ+,
        burnolCenteredMobiusReconstructionJointTerm source x (n, m) :=
      (Summable.tsum_comm (f := fun n : ℕ+ => fun m : ℕ+ =>
        burnolCenteredMobiusReconstructionJointTerm source x (n, m)) jointSummable)
    _ = ∑' index : ℕ+ × ℕ+,
        burnolCenteredMobiusReconstructionJointTerm source x index :=
      jointSummable.tsum_prod.symm
    _ = ∑' n : ℕ+, (((n : ℕ) : ℂ)⁻¹) *
        burnolCenteredMobiusInverse source (x / (n : ℕ)) :=
      (burnolCenteredMobiusForwardSum_eq_joint source quarterGap x).symm
    _ = source x := by
      rw [burnolCenteredMobiusInverse_exactReconstruction source quarterGap x, atZero, sub_zero]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
