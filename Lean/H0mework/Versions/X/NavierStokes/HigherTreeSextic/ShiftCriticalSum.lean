import H0mework.Versions.X.NavierStokes.HigherTreeSextic.CriticalSum
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.ShiftSchur

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticShiftCriticalSum
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativeUnheatedSexticLatticePower NativeUnheatedSexticRowSquare
open NativeUnheatedSexticCriticalSum (jointRoot jointRoot_positive jointRoot_square jointRoot_fourth jointRoot_tenth)
noncomputable section

def profile (wave r b c : IntegerWavevector) : ℝ :=
  (density 2 (wave-b-c)/Real.sqrt (pairMass b c))*(jointRoot r b c^5)⁻¹

theorem profile_nonnegative (wave r b c : IntegerWavevector) : 0 ≤ profile wave r b c := by
  unfold profile
  positivity [density_positive 2 (wave-b-c), pairMass_positive b c, jointRoot_positive r b c]

theorem profile_rpow (wave r b c : IntegerWavevector) :
    profile wave r b c = (density 2 (wave-b-c)/Real.sqrt (mass b+mass c))*(mass b+mass c+mass r)^(-5/4 : ℝ) := by
  have joint : jointRoot r b c = (pairMass b c+mass r)^(1/4 : ℝ) := by
    simp only [jointRoot, Real.sqrt_eq_rpow, ← Real.rpow_mul (add_pos (pairMass_positive b c) (mass_positive r)).le]
    norm_num
  rw [profile, joint, ← Real.rpow_mul_natCast (add_pos (pairMass_positive b c) (mass_positive r)).le,
    ← Real.rpow_neg (add_pos (pairMass_positive b c) (mass_positive r)).le]
  norm_num only
  rfl

theorem profile_square (wave r b c : IntegerWavevector) :
    profile wave r b c^2 = ((density 2 (wave-b-c))^2/pairMass b c)*decay (pairMass b c+mass r) := by
  simp only [profile, mul_pow, div_pow, inv_pow, ← pow_mul]
  rw [show 5*2 = 10 by omega, jointRoot_tenth, Real.sq_sqrt (pairMass_positive b c).le]
  rfl

theorem profile_fourth (wave r b c : IntegerWavevector) :
    profile wave r b c^4 = ((mass (wave-b-c))^2*(pairMass b c)^2*(pairMass b c+mass r)^5)⁻¹ := by
  have first : (density 2 (wave-b-c))^4 = ((mass (wave-b-c))^2)⁻¹ := by
    rw [density, inv_pow, ← pow_mul, show 2*4 = 4*2 by omega, pow_mul, radical_fourth]
  have middle : (Real.sqrt (pairMass b c))^4 = (pairMass b c)^2 := by
    rw [show (Real.sqrt (pairMass b c))^4 = ((Real.sqrt (pairMass b c))^2)^2 by ring,
      Real.sq_sqrt (pairMass_positive b c).le]
  have last : jointRoot r b c^20 = (pairMass b c+mass r)^5 := by
    rw [show 20 = 4*5 by omega, pow_mul, jointRoot_fourth]
  rw [profile, mul_pow, div_pow, first, middle, inv_pow, ← pow_mul, show 5*4 = 20 by omega, last]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem square_sum (wave b c : IntegerWavevector) (F : Finset IntegerWavevector) :
    (∑ r ∈ F, profile wave r b c^2) ≤ (16*NativeUnheatedSexticShiftSchur.kernel wave b c)^2 := by
  simp_rw [profile_square]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (decay_sum b c F)
    (div_nonneg (sq_nonneg _) (pairMass_positive b c).le)).trans_eq
  change (density 2 (wave-b-c))^2/pairMass b c*(256/pairMass b c) = (16*(density 2 (wave-b-c)/pairMass b c))^2
  field_simp [(pairMass_positive b c).ne']
  ring

abbrev term (wave : IntegerWavevector) (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :=
  NativeUnheatedSchurThree.term (profile wave) left middle right

theorem summable (wave : IntegerWavevector) (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :
    Summable (term wave left middle right) :=
  NativeUnheatedSchurThree.summable (profile wave) (NativeUnheatedSexticShiftSchur.kernel wave) 16
    (profile_nonnegative wave) (NativeUnheatedSexticShiftSchur.kernel_nonnegative wave) (by norm_num) (square_sum wave)
    (density 3) (NativeUnheatedSexticShiftSchur.cap wave) (density_positive 3) (NativeUnheatedSexticShiftSchur.cap_nonnegative wave)
    (NativeUnheatedSexticShiftSchur.row_bound wave) (NativeUnheatedSexticShiftSchur.column_bound wave) left middle right

theorem bound (wave : IntegerWavevector) (left middle right : NativeUnheatedSchur.Space IntegerWavevector) :
    (∑' index, term wave left middle right index) ≤ (16*NativeUnheatedSexticShiftSchur.cap wave)*‖left‖*‖middle‖*‖right‖ :=
  NativeUnheatedSchurThree.bound (profile wave) (NativeUnheatedSexticShiftSchur.kernel wave) 16
    (profile_nonnegative wave) (NativeUnheatedSexticShiftSchur.kernel_nonnegative wave) (by norm_num) (square_sum wave)
    (density 3) (NativeUnheatedSexticShiftSchur.cap wave) (density_positive 3) (NativeUnheatedSexticShiftSchur.cap_nonnegative wave)
    (NativeUnheatedSexticShiftSchur.row_bound wave) (NativeUnheatedSexticShiftSchur.column_bound wave) left middle right

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticShiftCriticalSum
