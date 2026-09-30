import H0mework.Versions.X.NavierStokes.HigherTreeSextic.QuarterSchur
import H0mework.NavierStokes.HigherTreeSextic.SchurThree
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.RowSquare

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticBalancedSum
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore NativeCompleteStressCarrier
open NativeUnheatedSexticLatticePower NativeUnheatedSexticRowSquare
noncomputable section

theorem mass_neg (wave : IntegerWavevector) : mass (-wave) = mass wave := by simp [mass, integerWaveNormSq]
theorem density_neg (power : ℕ) (wave : IntegerWavevector) : density power (-wave) = density power wave := by
  simp only [density, radical, mass_neg]

theorem weight_neg (wave : IntegerWavevector) : weight (-wave) = weight wave := by simp [weight, integerWaveNormSq]

theorem convolution_bound (wave : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ first ∈ observed, weight first*weight (wave-first)) ≤ NativeUnheatedRieszKernel.constant*density 2 wave := by
  rw [density, radical_square, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (mass_positive wave))).mpr
  simpa only [mass, mul_comm] using NativeUnheatedRieszKernel.finite_bound wave observed

def momentum (kind : Fin 2) (r a b : IntegerWavevector) : IntegerWavevector := if kind=0 then r else a+b+r

theorem paired_sum (kind : Fin 2) (a b : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ r ∈ observed, density 4 (momentum kind r a b)/(mass (a+b)+mass r)) ≤
      2*NativeUnheatedRieszKernel.constant*density 2 (a+b) := by
  by_cases zero : kind=0
  · have point (r : IntegerWavevector) : density 4 r/(mass (a+b)+mass r) ≤ 2*(weight r*weight (a+b-r)) := by
      have triangle := NativeUnheatedSexticShiftRiesz.mass_triangle (a+b) (-r)
      rw [mass_neg, ← sub_eq_add_neg] at triangle
      have inverse := inv_anti₀ (div_pos (mass_positive (a+b-r)) (by norm_num : (0 : ℝ) < 2))
        (show mass (a+b-r)/2 ≤ mass (a+b)+mass r by linarith)
      have scalar : (mass (a+b)+mass r)⁻¹ ≤ 2*density 4 (a+b-r) := by
        simpa only [density_four, one_div, div_eq_mul_inv, mul_inv_rev, inv_inv] using inverse
      have paid := mul_le_mul (density_four_le_weight r)
        (scalar.trans (mul_le_mul_of_nonneg_left (density_four_le_weight (a+b-r)) (by norm_num)))
        (inv_nonneg.mpr (add_pos (mass_positive _) (mass_positive _)).le) (weight_pos r).le
      exact paid.trans_eq (by ring)
    simp only [momentum, if_pos zero]
    have paid := Finset.sum_le_sum (s := observed) fun r _ => point r
    rw [← Finset.mul_sum] at paid
    exact paid.trans ((mul_le_mul_of_nonneg_left (convolution_bound (a+b) observed) (by norm_num)).trans_eq (by ring))
  · have point (r : IntegerWavevector) : density 4 (a+b+r)/(mass (a+b)+mass r) ≤ weight r*weight (-(a+b)-r) := by
      have lower := inv_anti₀ (mass_positive r) (show mass r ≤ mass (a+b)+mass r by linarith [mass_positive (a+b)])
      have paid := mul_le_mul (density_four_le_weight (a+b+r))
        (lower.trans (by simpa only [density_four] using density_four_le_weight r)) (inv_nonneg.mpr (add_pos (mass_positive _) (mass_positive _)).le)
        (weight_pos (a+b+r)).le
      have sign : -(a+b)-r = -(a+b+r) := by abel
      simpa only [div_eq_mul_inv, sign, weight_neg, mul_comm] using paid
    simp only [momentum, if_neg zero]
    have paid := (Finset.sum_le_sum (s := observed) fun r _ => point r).trans (convolution_bound (-(a+b)) observed)
    rw [density_neg] at paid
    exact paid.trans (by nlinarith [NativeUnheatedRieszKernel.constant_nonnegative, density_positive 2 (a+b)])

def pairRoot (a b : IntegerWavevector) : ℝ := Real.sqrt (Real.sqrt (pairMass a b))
theorem pairRoot_positive (a b : IntegerWavevector) : 0 < pairRoot a b := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (pairMass_positive a b))
theorem pairRoot_square (a b : IntegerWavevector) : pairRoot a b^2 = Real.sqrt (pairMass a b) := Real.sq_sqrt (Real.sqrt_nonneg _)
theorem pairRoot_fourth (a b : IntegerWavevector) : pairRoot a b^4 = pairMass a b := by
  rw [show pairRoot a b^4 = (pairRoot a b^2)^2 by ring, pairRoot_square, Real.sq_sqrt (pairMass_positive a b).le]

def profile (kind : Fin 2) (r a b : IntegerWavevector) : ℝ :=
  (density 2 (momentum kind r a b)/Real.sqrt (mass (a+b)+mass r))*(pairRoot a b^5)⁻¹

theorem profile_nonnegative (kind : Fin 2) (r a b : IntegerWavevector) : 0 ≤ profile kind r a b := by
  unfold profile
  positivity [density_positive 2 (momentum kind r a b), mass_positive (a+b), mass_positive r, pairRoot_positive a b]

theorem profile_square (kind : Fin 2) (r a b : IntegerWavevector) :
    profile kind r a b^2 = (density 4 (momentum kind r a b)/(mass (a+b)+mass r))*(pairRoot a b^10)⁻¹ := by
  rw [profile, mul_pow, div_pow, Real.sq_sqrt (add_pos (mass_positive _) (mass_positive _)).le,
    inv_pow, ← pow_mul, show (5 : ℕ)*2=10 by norm_num]
  rw [pow_two, ← density_add]

theorem profile_fourth (kind : Fin 2) (r a b : IntegerWavevector) :
    profile kind r a b^4 = ((mass (momentum kind r a b))^2*(mass (a+b)+mass r)^2*(pairMass a b)^5)⁻¹ := by
  have numerator : (density 2 (momentum kind r a b))^4 = ((mass (momentum kind r a b))^2)⁻¹ := by
    rw [density, inv_pow, ← pow_mul, show (2 : ℕ)*4=4*2 by norm_num, pow_mul, radical_fourth]
  have middle : (Real.sqrt (mass (a+b)+mass r))^4 = (mass (a+b)+mass r)^2 := by
    rw [show (Real.sqrt (mass (a+b)+mass r))^4 = ((Real.sqrt (mass (a+b)+mass r))^2)^2 by ring,
      Real.sq_sqrt (add_pos (mass_positive _) (mass_positive _)).le]
  rw [profile, mul_pow, div_pow, numerator, middle, inv_pow, ← pow_mul,
    show (5 : ℕ)*4=4*5 by norm_num, pow_mul, pairRoot_fourth]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem quarter_square (a b : IntegerWavevector) :
    NativeUnheatedSexticQuarterSchur.kernel 0 a b^2 = density 2 (a+b)*(pairRoot a b^10)⁻¹ := by
  have sign : (0 : IntegerWavevector)-a-b = -(a+b) := by abel
  have last : pairRoot a b^10 = (pairMass a b)^2*Real.sqrt (pairMass a b) := by
    rw [show pairRoot a b^10 = (pairRoot a b^4)^2*pairRoot a b^2 by ring, pairRoot_fourth, pairRoot_square]
  rw [NativeUnheatedSexticQuarterSchur.kernel_square]
  simp only [NativeUnheatedSexticShiftSchur.kernel, NativeUnheatedSexticQuarterSchur.base,
    sign, density_neg, last, pairMass, div_eq_mul_inv, mul_inv_rev]
  field_simp [(add_pos (mass_positive a) (mass_positive b)).ne']

def gain : ℝ := Real.sqrt (2*NativeUnheatedRieszKernel.constant)
theorem gain_nonnegative : 0 ≤ gain := Real.sqrt_nonneg _

theorem square_sum (kind : Fin 2) (a b : IntegerWavevector) (observed : Finset IntegerWavevector) :
    (∑ r ∈ observed, profile kind r a b^2) ≤ (gain*NativeUnheatedSexticQuarterSchur.kernel 0 a b)^2 := by
  simp_rw [profile_square]
  rw [← Finset.sum_mul, mul_pow, quarter_square]
  have paid := mul_le_mul_of_nonneg_right (paired_sum kind a b observed) (inv_nonneg.mpr (pow_nonneg (pairRoot_positive a b).le 10))
  rw [gain, Real.sq_sqrt (mul_nonneg (by norm_num) NativeUnheatedRieszKernel.constant_nonnegative)]
  exact paid.trans_eq (by ring)

def term (kind : Fin 2) (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :=
  NativeUnheatedSchurThree.term (profile kind) left middle right

theorem summable (kind : Fin 2) (left middle right : NativeUnheatedSchur.Space IntegerWavevector) : Summable (term kind left middle right) :=
  NativeUnheatedSchurThree.summable (profile kind) (NativeUnheatedSexticQuarterSchur.kernel 0) gain
    (profile_nonnegative kind) (NativeUnheatedSexticQuarterSchur.kernel_nonnegative 0) gain_nonnegative (square_sum kind)
    (density 3) (NativeUnheatedSexticQuarterSchur.cap 0) (density_positive 3) (NativeUnheatedSexticQuarterSchur.cap_nonnegative 0)
    (NativeUnheatedSexticQuarterSchur.row_bound 0) (NativeUnheatedSexticQuarterSchur.column_bound 0) left middle right

theorem bound (kind : Fin 2) (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, term kind left middle right index) ≤ gain*NativeUnheatedSexticQuarterSchur.cap 0*‖left‖*‖middle‖*‖right‖ :=
  NativeUnheatedSchurThree.bound (profile kind) (NativeUnheatedSexticQuarterSchur.kernel 0) gain
    (profile_nonnegative kind) (NativeUnheatedSexticQuarterSchur.kernel_nonnegative 0) gain_nonnegative (square_sum kind)
    (density 3) (NativeUnheatedSexticQuarterSchur.cap 0) (density_positive 3) (NativeUnheatedSexticQuarterSchur.cap_nonnegative 0)
    (NativeUnheatedSexticQuarterSchur.row_bound 0) (NativeUnheatedSexticQuarterSchur.column_bound 0) left middle right

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticBalancedSum
