import H0mework.Physics.LowEnergy.PacketField.Frame
import Mathlib.Analysis.Complex.Basic

/-! Every coefficient of the native degree-eight circle numerator is bounded
after its actual (1+t²)^4 denominator, uniformly in the frame parameter. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
noncomputable section

def circleCoefficient (degree : Fin 9) (parameter : ℝ) : ℝ :=
  parameter^degree.val/(1+parameter^2)^4

theorem circleCoefficient_bound (degree : Fin 9) (parameter : ℝ) : |circleCoefficient degree parameter|≤1 := by
  have positive : 0<(1+parameter^2)^4 := by positivity
  have power : |parameter|^degree.val≤(1+parameter^2)^4 := by
    by_cases small : |parameter|≤1
    · exact (pow_le_one₀ (abs_nonneg parameter) small).trans
        (one_le_pow₀ (by nlinarith [sq_nonneg parameter]))
    · calc
        _ ≤ |parameter|^8 := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge small)) (by omega)
        _ = (|parameter|^2)^4 := by ring
        _ ≤ (1+parameter^2)^4 := pow_le_pow_left₀ (sq_nonneg _) (by rw [sq_abs]; linarith) 4
  rw [circleCoefficient,abs_div,abs_pow,abs_of_pos positive]
  exact (div_le_one positive).mpr power

theorem circleCoefficient_continuous (degree : Fin 9) : Continuous (circleCoefficient degree) := by
  unfold circleCoefficient
  exact (continuous_pow degree.val).div ((continuous_const.add (continuous_pow 2)).pow 4)
    (fun parameter => ne_of_gt (by positivity))

def circleEntry (coefficients : Fin 9 → ℂ) (parameter : ℝ) : ℂ :=
  ∑ degree, coefficients degree*(circleCoefficient degree parameter : ℂ)

theorem circleEntry_bound (coefficients : Fin 9 → ℂ) (parameter : ℝ) :
    ‖circleEntry coefficients parameter‖≤∑ degree, ‖coefficients degree‖ := by
  unfold circleEntry
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro degree _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (circleCoefficient_bound degree parameter)

theorem circleEntry_continuous (coefficients : Fin 9 → ℂ) : Continuous (circleEntry coefficients) := by
  unfold circleEntry
  exact continuous_finsetSum _ (fun degree _ => continuous_const.mul
    (Complex.continuous_ofReal.comp (circleCoefficient_continuous degree)))

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
