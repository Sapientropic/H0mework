import H0mework.Versions.X.NavierStokes.HigherTreeSextic.RowSquare
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.Hardy
import H0mework.NavierStokes.HigherTreeSextic.SchurThree

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticCriticalSum
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeUnheatedSexticLatticePower NativeUnheatedSexticRowSquare
noncomputable section

def jointRoot (r b c : IntegerWavevector) : ℝ := Real.sqrt (Real.sqrt (pairMass b c+mass r))

theorem jointRoot_positive (r b c : IntegerWavevector) : 0 < jointRoot r b c :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (add_pos (pairMass_positive b c) (mass_positive r)))

theorem jointRoot_square (r b c : IntegerWavevector) :
    jointRoot r b c^2 = Real.sqrt (pairMass b c+mass r) := Real.sq_sqrt (Real.sqrt_nonneg _)

theorem jointRoot_fourth (r b c : IntegerWavevector) : jointRoot r b c^4 = pairMass b c+mass r := by
  rw [show jointRoot r b c^4 = (jointRoot r b c^2)^2 by ring, jointRoot_square,
    Real.sq_sqrt (add_pos (pairMass_positive b c) (mass_positive r)).le]

theorem jointRoot_tenth (r b c : IntegerWavevector) :
    jointRoot r b c^10 = (pairMass b c+mass r)^2*Real.sqrt (pairMass b c+mass r) := by
  rw [show jointRoot r b c^10 = (jointRoot r b c^4)^2*jointRoot r b c^2 by ring,
    jointRoot_fourth, jointRoot_square]

def profile (r b c : IntegerWavevector) : ℝ :=
  (density 2 c/Real.sqrt (pairMass b c))*(jointRoot r b c^5)⁻¹

theorem profile_nonnegative (r b c : IntegerWavevector) : 0 ≤ profile r b c := by
  unfold profile
  positivity [density_positive 2 c, pairMass_positive b c, jointRoot_positive r b c]

theorem profile_rpow (r b c : IntegerWavevector) :
    profile r b c = (density 2 c/Real.sqrt (mass b+mass c))*(mass b+mass c+mass r)^(-5/4 : ℝ) := by
  have joint : jointRoot r b c = (pairMass b c+mass r)^(1/4 : ℝ) := by
    simp only [jointRoot, Real.sqrt_eq_rpow, ← Real.rpow_mul (add_pos (pairMass_positive b c) (mass_positive r)).le]
    norm_num
  rw [profile, joint, ← Real.rpow_mul_natCast (add_pos (pairMass_positive b c) (mass_positive r)).le,
    ← Real.rpow_neg (add_pos (pairMass_positive b c) (mass_positive r)).le]
  norm_num only
  rfl

theorem profile_square (r b c : IntegerWavevector) :
    profile r b c^2 = ((density 2 c)^2/pairMass b c)*decay (pairMass b c+mass r) := by
  simp only [profile, mul_pow, div_pow, inv_pow, ← pow_mul]
  rw [show 5*2 = 10 by omega, jointRoot_tenth, Real.sq_sqrt (pairMass_positive b c).le]
  rfl

theorem profile_fourth (r b c : IntegerWavevector) :
    profile r b c^4 = ((mass c)^2*(pairMass b c)^2*(pairMass b c+mass r)^5)⁻¹ := by
  have first : (density 2 c)^4 = ((mass c)^2)⁻¹ := by
    rw [density, inv_pow, ← pow_mul, show 2*4 = 4*2 by omega, pow_mul, radical_fourth]
  have middle : (Real.sqrt (pairMass b c))^4 = (pairMass b c)^2 := by
    rw [show (Real.sqrt (pairMass b c))^4 = ((Real.sqrt (pairMass b c))^2)^2 by ring,
      Real.sq_sqrt (pairMass_positive b c).le]
  have last : jointRoot r b c^20 = (pairMass b c+mass r)^5 := by
    rw [show 20 = 4*5 by omega, pow_mul, jointRoot_fourth]
  rw [profile, mul_pow, div_pow, first, middle, inv_pow, ← pow_mul, show 5*4 = 20 by omega, last]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem square_sum (b c : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ r ∈ F, profile r b c^2) ≤ (16*NativeUnheatedSexticHardy.kernel b c)^2 := by
  simp_rw [profile_square]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (decay_sum b c F)
    (div_nonneg (sq_nonneg _) (pairMass_positive b c).le)).trans_eq
  change (density 2 c)^2/pairMass b c*(256/pairMass b c) = (16*(density 2 c/pairMass b c))^2
  field_simp [(pairMass_positive b c).ne']
  ring

abbrev term (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :=
  NativeUnheatedSchurThree.term profile left middle right

theorem summable (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :
    Summable (term left middle right) :=
  NativeUnheatedSchurThree.summable profile NativeUnheatedSexticHardy.kernel 16
    profile_nonnegative NativeUnheatedSexticHardy.kernel_nonnegative (by norm_num) square_sum
    (density 3) 512 (density_positive 3) (by norm_num)
    NativeUnheatedSexticHardy.row_bound NativeUnheatedSexticHardy.column_bound left middle right

theorem bound (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, term left middle right index) ≤ 8192*‖left‖*‖middle‖*‖right‖ := by
  have paid := NativeUnheatedSchurThree.bound profile NativeUnheatedSexticHardy.kernel 16
    profile_nonnegative NativeUnheatedSexticHardy.kernel_nonnegative (by norm_num) square_sum
    (density 3) 512 (density_positive 3) (by norm_num)
    NativeUnheatedSexticHardy.row_bound NativeUnheatedSexticHardy.column_bound left middle right
  norm_num only [show (16 : ℝ)*512 = 8192 by norm_num] at paid
  exact paid

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticCriticalSum
