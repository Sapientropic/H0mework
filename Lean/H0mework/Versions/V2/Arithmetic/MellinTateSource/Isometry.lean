import H0mework.Versions.V2.Arithmetic.MellinTateSource.L2Raw

/-! The same reciprocal is a norm-preserving linear involution on the original L² carrier. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace ENNReal
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "q" => (1 / 4 : ℝ)

theorem burnolTateReciprocalValue_add (left right : BurnolL2) :
    burnolTateReciprocalValue (left + right) =
      burnolTateReciprocalValue left + burnolTateReciprocalValue right := by
  have inputRead := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (left + right)) ((Lp.memLp left).add (Lp.memLp right))
    (Lp.coeFn_add left right)
  apply Lp.ext
  filter_upwards [burnolTateReciprocalValue_coeFn (left + right),
    burnolTateReciprocalValue_coeFn left,
    burnolTateReciprocalValue_coeFn right,
    Lp.coeFn_add (burnolTateReciprocalValue left)
      (burnolTateReciprocalValue right), inputRead]
    with x hsum hleft hright hadd hinput
  rw [hsum, hinput, hadd]
  change burnolTateReciprocalRaw (fun y ↦ left y + right y) x =
    burnolTateReciprocalValue left x +
      burnolTateReciprocalValue right x
  rw [hleft, hright]
  simp only [burnolTateReciprocalRaw]
  ring

theorem burnolTateReciprocalValue_smul (scalar : ℂ) (value : BurnolL2) :
    burnolTateReciprocalValue (scalar • value) =
      scalar • burnolTateReciprocalValue value := by
  have inputRead := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (scalar • value)) ((Lp.memLp value).const_smul scalar)
    (Lp.coeFn_smul scalar value)
  apply Lp.ext
  filter_upwards [burnolTateReciprocalValue_coeFn (scalar • value),
    burnolTateReciprocalValue_coeFn value,
    Lp.coeFn_smul scalar (burnolTateReciprocalValue value), inputRead]
    with x hscaled hvalue hsmul hinput
  rw [hscaled, hinput, hsmul]
  change burnolTateReciprocalRaw (fun y ↦ scalar * value y) x =
    scalar * burnolTateReciprocalValue value x
  rw [hvalue]
  simp only [burnolTateReciprocalRaw]
  ring

def burnolTateReciprocalLinear : BurnolL2 →ₗ[ℂ] BurnolL2 where
  toFun := burnolTateReciprocalValue
  map_add' := burnolTateReciprocalValue_add
  map_smul' := burnolTateReciprocalValue_smul

private theorem tateReciprocalNormSq_integral_pos (value : BurnolL2) :
    (∫ x : ℝ in Ioi 0, ‖burnolTateReciprocalRaw value x‖ ^ 2) =
      ∫ x : ℝ in Ioi 0, ‖value x‖ ^ 2 := by
  calc
    _ = ∫ x : ℝ in Ioi 0,
        (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
          ‖value (x ^ (-1 : ℝ))‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have positive : 0 < x := hx
      have nonzero : x ≠ 0 := positive.ne'
      simp only [burnolTateReciprocalRaw, norm_mul, norm_inv,
        norm_real, Real.norm_eq_abs, abs_of_pos positive, abs_neg,
        abs_one, one_mul, Real.rpow_neg_one, smul_eq_mul]
      rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
        Real.rpow_neg positive.le, Real.rpow_two]
      field_simp [nonzero]
    _ = _ := integral_comp_rpow_Ioi (fun x : ℝ ↦ ‖value x‖ ^ 2) (by norm_num)

private theorem tateReciprocalNormSq_integral_neg (value : BurnolL2) :
    (∫ x : ℝ in Iic 0, ‖burnolTateReciprocalRaw value x‖ ^ 2) =
      ∫ x : ℝ in Iic 0, ‖value x‖ ^ 2 := by
  calc
    _ = ∫ x : ℝ in Ioi 0,
        ‖burnolTateReciprocalRaw value (-x)‖ ^ 2 := by
      simpa only [neg_neg, neg_zero] using integral_comp_neg_Iic 0
        (fun x : ℝ ↦ ‖burnolTateReciprocalRaw value (-x)‖ ^ 2)
    _ = ∫ x : ℝ in Ioi 0,
        (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
          ‖value (-(x ^ (-1 : ℝ)))‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have positive : 0 < x := hx
      have nonzero : x ≠ 0 := positive.ne'
      simp only [burnolTateReciprocalRaw, norm_mul, norm_inv,
        norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos positive,
        abs_one, one_mul, Real.rpow_neg_one, smul_eq_mul]
      rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
        Real.rpow_neg positive.le, Real.rpow_two]
      field_simp [nonzero]
    _ = ∫ x : ℝ in Ioi 0, ‖value (-x)‖ ^ 2 :=
      integral_comp_rpow_Ioi (fun x : ℝ ↦ ‖value (-x)‖ ^ 2) (by norm_num)
    _ = _ := by simpa only [neg_zero] using
      integral_comp_neg_Ioi 0 (fun x : ℝ ↦ ‖value x‖ ^ 2)

private theorem tateReciprocalNormSq_integral (value : BurnolL2) :
    (∫ x : ℝ, ‖burnolTateReciprocalRaw value x‖ ^ 2) =
      ∫ x : ℝ, ‖value x‖ ^ 2 := by
  have transformed := (burnolTateReciprocalRaw_memLp value).integrable_norm_pow
    (by norm_num : 2 ≠ 0)
  have transformedNeg := transformed.integrableOn (s := Iic 0)
  have transformedPos := transformed.integrableOn (s := Ioi 0)
  have source := (Lp.memLp value).integrable_norm_pow (by norm_num : 2 ≠ 0)
  calc
    _ = (∫ x : ℝ in Iic 0, ‖burnolTateReciprocalRaw value x‖ ^ 2) +
        ∫ x : ℝ in Ioi 0, ‖burnolTateReciprocalRaw value x‖ ^ 2 := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        transformedNeg transformedPos, Iic_union_Ioi, setIntegral_univ]
    _ = (∫ x : ℝ in Iic 0, ‖value x‖ ^ 2) +
        ∫ x : ℝ in Ioi 0, ‖value x‖ ^ 2 := by
      rw [tateReciprocalNormSq_integral_neg,
        tateReciprocalNormSq_integral_pos]
    _ = _ := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        source.integrableOn source.integrableOn, Iic_union_Ioi, setIntegral_univ]

theorem burnolTateReciprocalValue_norm (value : BurnolL2) :
    ‖burnolTateReciprocalValue value‖ = ‖value‖ := by
  have square : ‖burnolTateReciprocalValue value‖ ^ 2 = ‖value‖ ^ 2 := by
    rw [burnolL2_norm_sq_eq_integral_norm_sq,
      burnolL2_norm_sq_eq_integral_norm_sq]
    calc
      _ = ∫ x : ℝ, ‖burnolTateReciprocalRaw value x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [burnolTateReciprocalValue_coeFn value]
          with x hx
        rw [hx]
      _ = _ := tateReciprocalNormSq_integral value
  nlinarith [norm_nonneg (burnolTateReciprocalValue value), norm_nonneg value]

/-- The Jacobian-corrected Tate involution as an actual norm-one `L²` map. -/
def burnolTateReciprocalL2 : BurnolL2 →L[ℂ] BurnolL2 :=
  LinearMap.mkContinuous burnolTateReciprocalLinear 1 fun value ↦ by
    change ‖burnolTateReciprocalValue value‖ ≤ 1 * ‖value‖
    rw [burnolTateReciprocalValue_norm, one_mul]

theorem burnolTateReciprocalL2_coeFn (value : BurnolL2) :
    (burnolTateReciprocalL2 value : ℝ → ℂ) =ᵐ[volume]
      burnolTateReciprocalRaw value :=
  burnolTateReciprocalValue_coeFn value

theorem burnolTateReciprocalL2_involutive (value : BurnolL2) :
    burnolTateReciprocalL2 (burnolTateReciprocalL2 value) = value := by
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (burnolTateReciprocalL2 value))
    (burnolTateReciprocalRaw_memLp value)
    (burnolTateReciprocalL2_coeFn value)
  apply Lp.ext
  filter_upwards [burnolTateReciprocalL2_coeFn
      (burnolTateReciprocalL2 value), pulled, volume.ae_ne (0 : ℝ)]
    with x houter hpulled hx
  rw [houter, hpulled]
  unfold burnolTateReciprocalRaw
  rw [inv_inv, abs_inv]
  push_cast
  field_simp [abs_ne_zero.mpr hx]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
