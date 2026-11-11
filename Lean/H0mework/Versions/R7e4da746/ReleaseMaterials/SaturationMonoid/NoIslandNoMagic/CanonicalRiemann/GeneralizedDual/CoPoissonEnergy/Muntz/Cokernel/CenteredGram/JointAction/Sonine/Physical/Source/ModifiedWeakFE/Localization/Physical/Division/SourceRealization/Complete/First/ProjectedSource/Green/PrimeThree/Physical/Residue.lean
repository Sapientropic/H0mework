import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.UnitShellPrimitive

/-! The prime-three residue is the actual two-sided physical dilation action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def primeThreePhysicalResidue (value : BurnolL2) : BurnolL2 :=
  let h := Real.log (Real.sqrt 3)
  let c : ℂ := (Real.sqrt (Real.sqrt 3) : ℝ)
  c • burnolMultiplicativeDilation h value -
    c⁻¹ • burnolMultiplicativeDilation (-h) value

theorem primeThreePhysicalResidue_coeFn (value : BurnolL2) :
    (primeThreePhysicalResidue value : ℝ → ℂ) =ᵐ[volume] fun x =>
      (Real.sqrt 3 : ℂ) * value (Real.sqrt 3 * x) -
        (Real.sqrt 3 : ℂ)⁻¹ * value (x / Real.sqrt 3) := by
  let a := Real.sqrt 3
  let h := Real.log a
  let c : ℂ := (Real.sqrt a : ℝ)
  have positive : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have expAt : Real.exp h = a := Real.exp_log positive
  have half : Real.exp (h / 2) = Real.sqrt a := by
    symm
    rw [Real.sqrt_eq_iff_eq_sq positive.le (Real.exp_nonneg _),
      sq, ← Real.exp_add, add_halves, expAt]
  have negativeHalf : Real.exp (-h / 2) = (Real.sqrt a)⁻¹ := by
    rw [neg_div, Real.exp_neg, half]
  have squared : c * c = (a : ℂ) := by
    change (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ)
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt positive.le]
  have inverseSquared : c⁻¹ * c⁻¹ = (a : ℂ)⁻¹ := by
    rw [← mul_inv, squared]
  change ((c • burnolMultiplicativeDilation h value -
    c⁻¹ • burnolMultiplicativeDilation (-h) value : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (c • burnolMultiplicativeDilation h value)
      (c⁻¹ • burnolMultiplicativeDilation (-h) value),
    Lp.coeFn_smul c (burnolMultiplicativeDilation h value),
    Lp.coeFn_smul c⁻¹ (burnolMultiplicativeDilation (-h) value),
    burnolMultiplicativeDilation_coeFn h value,
    burnolMultiplicativeDilation_coeFn (-h) value] with x hsub hpos hneg posAt negAt
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hpos hneg
  rw [hsub, hpos, hneg]
  change c * burnolMultiplicativeDilation h value x -
    c⁻¹ * burnolMultiplicativeDilation (-h) value x = _
  rw [posAt, negAt]
  unfold burnolL2RawNormalizedDilation
  rw [half, negativeHalf, expAt, Real.exp_neg, expAt, Complex.ofReal_inv]
  change c * (c * value (a * x)) - c⁻¹ * (c⁻¹ * value (a⁻¹ * x)) = _
  rw [← mul_assoc, squared, ← mul_assoc, inverseSquared, inv_mul_eq_div]
  simp only [a, inv_mul_eq_div]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
