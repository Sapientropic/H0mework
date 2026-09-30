import H0mework.Versions.X.NavierStokes.HigherTreeSextic.WeightedSquare
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CriticalSum
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.ShiftSchur

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticRootBalancedSum
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeUnheatedSexticLatticePower NativeUnheatedSexticRowSquare
open NativeUnheatedSexticCriticalSum (jointRoot jointRoot_positive jointRoot_fourth jointRoot_tenth)
noncomputable section

def profile (r a b : IntegerWavevector) : ℝ :=
  (density 2 (a+b)/Real.sqrt (mass (a+b)+mass r))*(jointRoot r a b^5)⁻¹

theorem profile_nonnegative (r a b : IntegerWavevector) : 0 ≤ profile r a b := by
  unfold profile
  positivity [density_positive 2 (a+b), mass_positive (a+b), mass_positive r, jointRoot_positive r a b]

theorem profile_square (r a b : IntegerWavevector) :
    profile r a b^2 = (density 4 (a+b)/(mass (a+b)+mass r))*decay (pairMass a b+mass r) := by
  rw [profile, mul_pow, div_pow, Real.sq_sqrt (add_pos (mass_positive _) (mass_positive _)).le,
    inv_pow, ← pow_mul, show (5 : ℕ)*2=10 by norm_num, jointRoot_tenth]
  rw [pow_two, ← density_add]
  rfl

theorem profile_fourth (r a b : IntegerWavevector) :
    profile r a b^4 = ((mass (a+b))^2*(mass (a+b)+mass r)^2*(pairMass a b+mass r)^5)⁻¹ := by
  have numerator : (density 2 (a+b))^4 = ((mass (a+b))^2)⁻¹ := by
    rw [density, inv_pow, ← pow_mul, show (2 : ℕ)*4=4*2 by norm_num, pow_mul, radical_fourth]
  have middle : (Real.sqrt (mass (a+b)+mass r))^4 = (mass (a+b)+mass r)^2 := by
    rw [show (Real.sqrt (mass (a+b)+mass r))^4 = ((Real.sqrt (mass (a+b)+mass r))^2)^2 by ring,
      Real.sq_sqrt (add_pos (mass_positive _) (mass_positive _)).le]
  rw [profile, mul_pow, div_pow, numerator, middle, inv_pow, ← pow_mul,
    show (5 : ℕ)*4=4*5 by norm_num, pow_mul, jointRoot_fourth]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem half_square (a b : IntegerWavevector) :
    NativeUnheatedSexticShiftSchur.kernel 0 a b^2 = density 4 (a+b)/(pairMass a b)^2 := by
  have sign : (0 : IntegerWavevector)-a-b = -(a+b) := by abel
  have massSign : mass (-(a+b)) = mass (a+b) := by
    simp only [mass, ThreeDimensionalVorticityCoefficientRawSourceCore.integerWaveNormSq, Pi.neg_apply, Int.cast_neg, neg_sq]
  rw [NativeUnheatedSexticShiftSchur.kernel, div_pow, pow_two, ← density_add, sign]
  simp only [density, radical, massSign, pairMass]

theorem square_sum (a b : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ r ∈ observed, profile r a b^2) ≤ (64*NativeUnheatedSexticShiftSchur.kernel 0 a b)^2 := by
  have point (r : IntegerWavevector) : profile r a b^2 ≤ density 4 (a+b)*
      (density 4 r*decay (pairMass a b+mass r)) := by
    rw [profile_square]
    have inverse := inv_anti₀ (mass_positive r) (show mass r ≤ mass (a+b)+mass r by linarith [mass_positive (a+b)])
    have paid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left inverse (density_positive 4 (a+b)).le)
      (decay_nonnegative (pairMass a b+mass r))
    simpa only [div_eq_mul_inv, density_four, mul_assoc] using paid
  have compared := Finset.sum_le_sum (s := observed) fun r _ => point r
  rw [← Finset.mul_sum] at compared
  have paid := mul_le_mul_of_nonneg_left (NativeUnheatedSexticWeightedSquare.finite_bound a b observed) (density_positive 4 (a+b)).le
  rw [mul_pow, half_square]
  exact compared.trans (paid.trans_eq (by ring))

def term (left middle right : NativeUnheatedSchur.Space IntegerWavevector) := NativeUnheatedSchurThree.term profile left middle right

theorem summable (left middle right : NativeUnheatedSchur.Space IntegerWavevector) : Summable (term left middle right) :=
  NativeUnheatedSchurThree.summable profile (NativeUnheatedSexticShiftSchur.kernel 0) 64 profile_nonnegative
    (NativeUnheatedSexticShiftSchur.kernel_nonnegative 0) (by norm_num) square_sum
    (density 3) (NativeUnheatedSexticShiftSchur.cap 0) (density_positive 3) (NativeUnheatedSexticShiftSchur.cap_nonnegative 0)
    (NativeUnheatedSexticShiftSchur.row_bound 0) (NativeUnheatedSexticShiftSchur.column_bound 0) left middle right

theorem bound (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, term left middle right index) ≤ 64*NativeUnheatedSexticShiftSchur.cap 0*‖left‖*‖middle‖*‖right‖ :=
  NativeUnheatedSchurThree.bound profile (NativeUnheatedSexticShiftSchur.kernel 0) 64 profile_nonnegative
    (NativeUnheatedSexticShiftSchur.kernel_nonnegative 0) (by norm_num) square_sum
    (density 3) (NativeUnheatedSexticShiftSchur.cap 0) (density_positive 3) (NativeUnheatedSexticShiftSchur.cap_nonnegative 0)
    (NativeUnheatedSexticShiftSchur.row_bound 0) (NativeUnheatedSexticShiftSchur.column_bound 0) left middle right

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticRootBalancedSum
