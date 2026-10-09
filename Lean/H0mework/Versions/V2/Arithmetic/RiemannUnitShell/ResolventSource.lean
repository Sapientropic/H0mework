import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.UnitResponseSource
import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.GeneratorResolvent

/-! An exact scale change expresses the original unit response through one fixed counting primitive, without a zero or landing premise. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem halfExp_image :
    (fun h : ℝ => Real.exp (-h / 2)) '' Ioi 0 = Ioo (0 : ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨h, positive, rfl⟩
    change 0 < h at positive
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  · intro inside
    refine ⟨-2 * Real.log u, ?_, ?_⟩
    · have negative := Real.log_neg inside.1 inside.2
      change 0 < -2 * Real.log u
      linarith
    · change Real.exp (-(-2 * Real.log u) / 2) = u
      rw [show -(-2 * Real.log u) / 2 = Real.log u by ring, Real.exp_log inside.1]

private theorem integral_halfExp (g : ℝ → BurnolL2) :
    (∫ u : ℝ in Ioc (0 : ℝ) 1, g u) =
      ∫ h : ℝ in Ioi (0 : ℝ), (Real.exp (-h / 2) / 2) • g (Real.exp (-h / 2)) := by
  have derivative (h : ℝ) : HasDerivAt (fun h : ℝ => Real.exp (-h / 2))
      (-Real.exp (-h / 2) / 2) h := by
    convert! (((hasDerivAt_id h).neg.div_const 2).exp) using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  rw [integral_Ioc_eq_integral_Ioo, ← halfExp_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun h _ => (derivative h).hasDerivWithinAt)
      (fun x _ y _ equal => by have same := Real.exp_injective equal; linarith)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  change |-Real.exp (-h / 2) / 2| • g (Real.exp (-h / 2)) = _
  rw [abs_of_nonpos (by have := Real.exp_pos (-h / 2); linarith)]
  congr 1
  ring

private theorem slope_halfExp (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (h : ℝ) :
    (Real.exp (-h / 2) / 2) •
        (burnolUnitTailSlope coordinate (Real.exp (-h / 2)) •
          burnolSourceScalePrimitive value (Real.exp (-h / 2))) =
      (-(coordinate.value - 1) / 2) •
        burnolDirectRightResolventIntegrand (coordinate.value / 2) value h := by
  have root : Real.sqrt (Real.exp (-h / 2)) = Real.exp (-h / 4) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have power : (Real.exp (-h / 2) : ℂ) ^ (coordinate.value - 2) =
      Complex.exp ((-(h : ℂ) / 2) * (coordinate.value - 2)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
    push_cast
    rfl
  unfold burnolUnitTailSlope burnolSourceScalePrimitive burnolDirectRightResolventIntegrand
  rw [root, Real.log_exp, power]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  apply congrArg (fun scalar : ℂ => scalar • burnolMultiplicativeDilation (-h / 2) value)
  unfold positiveMellinQuarterRightResolventWeight
  change ((Real.exp (-h / 2) / 2 : ℝ) : ℂ) *
    ((-(coordinate.value - 1) * Complex.exp ((-(h : ℂ) / 2) * (coordinate.value - 2))) *
      (Real.exp (-h / 4) : ℂ)) = _
  rw [Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_exp]
  norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  calc
    _ = (-(coordinate.value - 1) / 2) *
        (Complex.exp (-(h : ℂ) / 2) *
          Complex.exp ((-(h : ℂ) / 2) * (coordinate.value - 2)) *
          Complex.exp (-(h : ℂ) / 4)) := by ring
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      ring

theorem burnolUnitTailPrimitive_eq_fixedResolvent (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    burnolUnitTailPrimitiveValue coordinate value 1 =
      -value - ((coordinate.value - 1) / 2) • burnolDirectRightResolvent (coordinate.value / 2) value := by
  have integralRead :
      (∫ u : ℝ in Ioc (0 : ℝ) 1, burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive value u) =
        ((coordinate.value - 1) / 2) • burnolDirectRightResolvent (coordinate.value / 2) value := by
    rw [integral_halfExp]
    simp_rw [slope_halfExp]
    rw [integral_smul]
    unfold burnolDirectRightResolvent
    module
  unfold burnolUnitTailPrimitiveValue
  rw [integralRead]
  simp [burnolUnitPowerWeight, burnolSourceScalePrimitive, burnolMultiplicativeDilation_zero]

/-- The original unit response uses one counting primitive for every admitted coordinate. -/
theorem burnolUnitTailResponse_one_eq_fixedResolvent (coordinate : BurnolCompletedMellinCoordinate) :
    burnolUnitTailResponse coordinate 1 =
      -burnolUnitCountingPrimitiveL2 -
        ((coordinate.value - 1) / 2) •
          burnolDirectRightResolvent (coordinate.value / 2) burnolUnitCountingPrimitiveL2 := by
  simpa only [burnolUnitTailResponse, inv_one] using
    burnolUnitTailPrimitive_eq_fixedResolvent coordinate burnolUnitCountingPrimitiveL2

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
