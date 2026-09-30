import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.ResolventPhysical

/-! The actual reciprocal primitive and its Tate box are a single L² resolvent.
The source profile is calculated inside the Bochner integral, not supplied as a domain certificate. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem tatePrimitive_coeFn :
    (burnolTateReciprocalL2 burnolUnitReciprocalPrimitiveL2 : ℝ → ℂ) =ᵐ[volume]
      fun x => if |x| < 1 then (1 : ℂ) else 0 := by
  have rawMem := (Lp.memLp burnolUnitReciprocalPrimitiveL2).ae_eq burnolUnitReciprocalPrimitive_coeFn
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp burnolUnitReciprocalPrimitiveL2)
    rawMem burnolUnitReciprocalPrimitive_coeFn
  filter_upwards [burnolTateReciprocalL2_coeFn burnolUnitReciprocalPrimitiveL2, pulled,
    volume.ae_ne (0 : ℝ)] with x actual profile nonzero
  rw [actual, profile]
  unfold burnolTateReciprocalRaw burnolUnitReciprocalPrimitiveRaw
  have positive := abs_pos.mpr nonzero
  have condition : 1 < |x⁻¹| ↔ |x| < 1 := by
    rw [abs_inv, one_lt_inv₀ positive]
  simp only [condition]
  split_ifs
  · simp only [abs_inv, Complex.ofReal_inv, inv_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne')
  · exact mul_zero _

private def boxOrbitRaw (h x : ℝ) : ℂ :=
  if |x| < Real.exp (h / 2) then Complex.exp ((-1 / 2 : ℂ) * (h : ℂ)) else 0

private theorem boxOrbitIntegral (x : ℝ) (nonzero : x ≠ 0) (notUnit : |x| ≠ 1) :
    (∫ h : ℝ in Ioi 0, boxOrbitRaw h x) =
      (2 : ℂ) * (burnolUnitReciprocalPrimitiveRaw x + if |x| < 1 then 1 else 0) := by
  have positive := abs_pos.mpr nonzero
  by_cases small : |x| < 1
  · have same : (fun h => boxOrbitRaw h x) =ᵐ[volume.restrict (Ioi 0)]
        fun h => Complex.exp ((-1 / 2 : ℂ) * (h : ℂ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      change 0 < h at hh
      apply if_pos
      exact small.trans (Real.one_lt_exp_iff.mpr (by linarith : 0 < h / 2))
    rw [integral_congr_ae same, integral_exp_mul_complex_Ioi (by norm_num)]
    simp [burnolUnitReciprocalPrimitiveRaw, small, not_lt.mpr small.le]
  · have large : 1 < |x| := lt_of_le_of_ne (le_of_not_gt small) notUnit.symm
    have logPos := Real.log_pos large
    have same : (fun h => boxOrbitRaw h x) = (Ioi (2 * Real.log |x|)).indicator
        (fun h => Complex.exp ((-1 / 2 : ℂ) * (h : ℂ))) := by
      funext h
      have condition : |x| < Real.exp (h / 2) ↔ 2 * Real.log |x| < h := by
        rw [← Real.log_lt_iff_lt_exp positive]
        constructor <;> intro hh <;> linarith
      simp [boxOrbitRaw, indicator_apply, condition]
    rw [same, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have intersect : Ioi (2 * Real.log |x|) ∩ Ioi (0 : ℝ) = Ioi (2 * Real.log |x|) := by
      apply inter_eq_left.mpr
      intro h hh
      change 2 * Real.log |x| < h at hh
      change 0 < h
      linarith
    rw [intersect, integral_exp_mul_complex_Ioi (by norm_num)]
    have exponent : (-1 / 2 : ℂ) * ((2 * Real.log |x| : ℝ) : ℂ) = -(Real.log |x| : ℂ) := by
      push_cast
      ring
    rw [exponent, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log positive]
    simp [burnolUnitReciprocalPrimitiveRaw, large, small]
    ring

private theorem boxOrbit_coeFn (h : ℝ) :
    (burnolDirectRightResolventIntegrand (1 / 2)
      (burnolTateReciprocalL2 burnolUnitReciprocalPrimitiveL2) h : ℝ → ℂ) =ᵐ[volume] boxOrbitRaw h := by
  let box := burnolTateReciprocalL2 burnolUnitReciprocalPrimitiveL2
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-h / 2) * x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := Real.exp (-h / 2)) (Real.exp_ne_zero _))
  filter_upwards [Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight (1 / 2) h)
    (burnolMultiplicativeDilation (-h / 2) box),
    burnolMultiplicativeDilation_coeFn (-h / 2) box, qmp.ae tatePrimitive_coeFn]
      with x scalar acted profile
  change (positiveMellinQuarterRightResolventWeight (1 / 2) h •
    burnolMultiplicativeDilation (-h / 2) box : BurnolL2) x = _
  rw [scalar]
  change positiveMellinQuarterRightResolventWeight (1 / 2) h *
    burnolMultiplicativeDilation (-h / 2) box x = _
  rw [acted]
  unfold burnolL2RawNormalizedDilation
  rw [profile]
  have incidence : |Real.exp (-h / 2) * x| < 1 ↔ |x| < Real.exp (h / 2) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ← lt_div_iff₀' (Real.exp_pos _)]
    simp only [one_div, ← Real.exp_neg, neg_div, neg_neg]
  simp only [incidence]
  split_ifs with inside
  · simp only [mul_one, boxOrbitRaw, inside, if_true]
    unfold positiveMellinQuarterRightResolventWeight
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [boxOrbitRaw, inside]

theorem burnolReciprocalPrimitivePair_eq_boxResolvent :
    burnolUnitReciprocalPrimitiveL2 +
      burnolTateReciprocalL2 burnolUnitReciprocalPrimitiveL2 =
      (-1 / 2 : ℂ) • burnolDirectRightResolvent (1 / 2)
        (burnolTateReciprocalL2 burnolUnitReciprocalPrimitiveL2) := by
  let box := burnolTateReciprocalL2 burnolUnitReciprocalPrimitiveL2
  let family := burnolDirectRightResolventIntegrand (1 / 2) box
  have rawMeasured : Measurable (fun point : ℝ × ℝ => boxOrbitRaw point.1 point.2) := by
    unfold boxOrbitRaw
    exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop) measurable_const
  have reads : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)),
      (family h : ℝ → ℂ) =ᵐ[volume] boxOrbitRaw h := by
    exact Filter.Eventually.of_forall boxOrbit_coeFn
  have integrable : IntegrableOn family (Ioi 0) :=
    burnolDirectRightResolventIntegrand_integrableOn (1 / 2) (by norm_num) box
  apply ext_inner_left ℂ
  intro test
  have actual := burnolL2Bochner_pairing_raw (volume.restrict (Ioi (0 : ℝ))) family integrable
    (fun point => boxOrbitRaw point.1 point.2) rawMeasured reads test
  have formula : inner ℂ test (∫ h : ℝ in Ioi (0 : ℝ), family h) =
      (2 : ℂ) * inner ℂ test (burnolUnitReciprocalPrimitiveL2 + box) := by
    rw [actual.2, L2.inner_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [burnolUnitReciprocalPrimitive_coeFn, tatePrimitive_coeFn,
      Lp.coeFn_add burnolUnitReciprocalPrimitiveL2 box,
      volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ), volume.ae_ne (-1 : ℝ)]
        with x primitive boxAt sumAt nonzero notRight notLeft
    have notUnit : |x| ≠ 1 := by
      intro equal
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp equal with h | h
      · exact notRight h
      · exact notLeft h
    rw [boxOrbitIntegral x nonzero notUnit, sumAt]
    change inner ℂ (test x) ((2 : ℂ) * _) =
      (2 : ℂ) * inner ℂ (test x) (burnolUnitReciprocalPrimitiveL2 x + box x)
    rw [primitive, boxAt]
    exact inner_smul_right (𝕜 := ℂ) _ _ _
  rw [inner_smul_right, burnolDirectRightResolvent, inner_neg_right, formula]
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
