import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedSlopePrice

set_option autoImplicit false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPreparedPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse ActualDressedNumberSector ActualDressedNumberZero
open ActualDressedSourcePreparation
open scoped Topology BigOperators
attribute [local irreducible] numberTwoProjection actualA physicalTime timeSlope jointCurrent sourceDressedUnit

theorem occupationPrice_two (a T : ℝ) : occupationPrice 2 a T=1+T*a+(T*a)^2 := by
  simp [occupationPrice,Finset.sum_range_succ]

theorem occupationPrice_two_growth (a T : ℝ) (ha : 0  ≤  a) (hT : 0  ≤  T) :
    occupationPrice 2 a T  ≤  (1+a)^2*(1+T)^2 := by
  calc
    _=1+T*a+(T*a)^2:=occupationPrice_two a T
    _  ≤  (1+T*a)^2:=by nlinarith [mul_nonneg hT ha]
    _  ≤  ((1+a)*(1+T))^2:=pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    _=_:=by ring

private theorem scalar_slope_growth (a J V T : ℝ)
    (ha : 0 ≤ a) (hJ : 0 ≤ J) (hV : 0 ≤ V) (hT : 0 ≤ T) :
    T*J*(occupationPrice 2 a T)^2*V ≤ (J*(1+a)^4*V)*(1+T)^5 := by
  have hP:=occupationPrice_nonneg 2 a T ha hT
  have square : (occupationPrice 2 a T)^2 ≤ (1+a)^4*(1+T)^4:=
    (pow_le_pow_left₀ hP (occupationPrice_two_growth a T ha hT) 2).trans_eq (by ring)
  calc
    _ ≤ ((1+T)*J)*((1+a)^4*(1+T)^4)*V:=by
      apply mul_le_mul_of_nonneg_right _ hV
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hJ) square
        (sq_nonneg _) (by positivity)
    _=_:=by ring

theorem actual_timeSlope_N2_polynomial_price (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (force : Field289) (v : H)
    (sector : numberTwoProjection v=v) (t : ℝ) :
    ‖timeSlope force p F t v‖ ≤
      (‖jointCurrent p F 0 0 force‖*(1+‖actualA p F‖)^4*‖v‖)*(1+|t|)^5 :=
  (actual_timeSlope_N2_price p F force t v sector).trans
    (scalar_slope_growth ‖actualA p F‖ ‖jointCurrent p F 0 0 force‖ ‖v‖ |t|
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (abs_nonneg t))

theorem actual_created_timeSlope_polynomial_price (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (force : Field289) (epsilon : ℝ) (precision : 0<epsilon)
    (t : ℝ) :
    ‖timeSlope force p F t (sourceDressedUnit epsilon precision)‖  ≤
      (‖jointCurrent p F 0 0 force‖*(1+‖actualA p F‖)^4)*(1+|t|)^5 := by
  simpa only [source_dressed_unit_norm,mul_one] using actual_timeSlope_N2_polynomial_price
    p F force (sourceDressedUnit epsilon precision) (actual_created_unit_N2 epsilon precision) t

end LowEnergy.GaussComposite.ActualDressedPreparedPrice
