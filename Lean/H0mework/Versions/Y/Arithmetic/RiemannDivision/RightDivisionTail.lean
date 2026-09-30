import H0mework.Versions.Y.Arithmetic.RiemannDivision.DirectRightResolvent

/-! # Burnol right-division tail calculus -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set Filter FourierTransform
open SourceGeneratedComplexFeaturePerfectification
open scoped ENNReal InnerProductSpace

noncomputable section

def burnolFourierRightDivisionRaw
    (z : ℂ) (value : ℝ → ℂ) (x : ℝ) : ℂ :=
  -∫ h : ℝ in Ioi (0 : ℝ),
    Complex.exp (((1 / 2 : ℂ) - z) * (h : ℂ)) *
      value (Real.exp (h / 2) * x)

theorem burnolFourierRightDivision_integrand_eq
    (z : ℂ) (value : BurnolL2) (x h : ℝ) :
    positiveMellinQuarterRightResolventWeight z h *
        burnolL2RawNormalizedDilation (h / 2) value x =
      Complex.exp (((1 / 2 : ℂ) - z) * (h : ℂ)) *
        value (Real.exp (h / 2) * x) := by
  unfold positiveMellinQuarterRightResolventWeight
    burnolL2RawNormalizedDilation
  rw [Complex.ofReal_exp]
  calc
    Complex.exp (((1 / 4 : ℂ) - z) * (h : ℂ)) *
        (Complex.exp ((h / 2 / 2 : ℝ) : ℂ) *
          value (Real.exp (h / 2) * x)) =
      (Complex.exp (((1 / 4 : ℂ) - z) * (h : ℂ)) *
        Complex.exp ((h / 2 / 2 : ℝ) : ℂ)) *
          value (Real.exp (h / 2) * x) := by ring
    _ = Complex.exp
        ((((1 / 4 : ℂ) - z) * (h : ℂ)) +
          ((h / 2 / 2 : ℝ) : ℂ)) *
          value (Real.exp (h / 2) * x) := by rw [← Complex.exp_add]
    _ = _ := by
      apply congrArg (fun coefficient : ℂ =>
        coefficient * value (Real.exp (h / 2) * x))
      apply congrArg Complex.exp
      push_cast
      ring

theorem burnolFourierRightDivisionRaw_scale_two
    (z : ℂ) (value : ℝ → ℂ) (x : ℝ) :
    burnolFourierRightDivisionRaw z value x =
      -2 * ∫ y : ℝ in Ioi (0 : ℝ),
        Complex.exp (((1 : ℂ) - 2 * z) * (y : ℂ)) *
          value (Real.exp y * x) := by
  let integrand : ℝ → ℂ := fun h =>
    Complex.exp (((1 / 2 : ℂ) - z) * (h : ℂ)) *
      value (Real.exp (h / 2) * x)
  have change := MeasureTheory.integral_comp_mul_left_Ioi
    integrand 0 (b := (2 : ℝ)) (by norm_num)
  have integrandTwo : (fun y : ℝ => integrand (2 * y)) =
      fun y : ℝ =>
        Complex.exp (((1 : ℂ) - 2 * z) * (y : ℂ)) *
          value (Real.exp y * x) := by
    funext y
    dsimp only [integrand]
    rw [show (2 * y) / 2 = y by ring]
    apply congrArg (fun coefficient : ℂ =>
      coefficient * value (Real.exp y * x))
    apply congrArg Complex.exp
    push_cast
    ring
  rw [integrandTwo] at change
  unfold burnolFourierRightDivisionRaw
  change -(∫ h : ℝ in Ioi (0 : ℝ), integrand h) = _
  simp only [mul_zero] at change
  rw [change]
  norm_num [smul_eq_mul]
  ring

theorem exp_mul_cpow_neg_two (z : ℂ) (y : ℝ) :
    Complex.exp (((1 : ℂ) - 2 * z) * (y : ℂ)) =
      (Real.exp y : ℂ) * (Real.exp y : ℂ) ^ (-2 * z) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero y))]
  rw [← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp,
    Complex.ofReal_exp, ← Complex.exp_add]
  apply congrArg Complex.exp
  ring

theorem burnolFourierRightDivisionRaw_exp_change
    (z : ℂ) (value : ℝ → ℂ) (x : ℝ) :
    burnolFourierRightDivisionRaw z value x =
      -2 * ∫ u : ℝ in Ioi (1 : ℝ),
        (u : ℂ) ^ (-2 * z) * value (u * x) := by
  rw [burnolFourierRightDivisionRaw_scale_two]
  have change := MeasureTheory.integral_comp_exp_Ioi
    (fun u : ℝ => (u : ℂ) ^ (-2 * z) * value (u * x)) 0
  have sourceEq : (fun y : ℝ =>
      Real.exp y • ((Real.exp y : ℂ) ^ (-2 * z) *
        value (Real.exp y * x))) =
      fun y : ℝ =>
        Complex.exp (((1 : ℂ) - 2 * z) * (y : ℂ)) *
          value (Real.exp y * x) := by
    funext y
    simp only [Complex.real_smul]
    rw [exp_mul_cpow_neg_two]
    ring
  rw [sourceEq] at change
  simpa using congrArg (fun current : ℂ => (-2 : ℂ) * current) change

theorem burnolFourierRightDivision_tail_change
    (z : ℂ) (value : ℝ → ℂ) {x : ℝ} (positiveX : 0 < x) :
    (∫ u : ℝ in Ioi (1 : ℝ),
        (u : ℂ) ^ (-2 * z) * value (u * x)) =
      (x : ℂ) ^ (2 * z - 1) *
        ∫ t : ℝ in Ioi x, (t : ℂ) ^ (-2 * z) * value t := by
  let weighted : ℝ → ℂ := fun t => (t : ℂ) ^ (-2 * z) * value t
  have change := MeasureTheory.integral_comp_mul_right_Ioi weighted 1 positiveX
  have integrandEq : ∀ u : ℝ, u ∈ Ioi (1 : ℝ) →
      (u : ℂ) ^ (-2 * z) * value (u * x) =
        (x : ℂ) ^ (2 * z) * weighted (u * x) := by
    intro u positiveU
    dsimp only [weighted]
    rw [Complex.ofReal_mul,
      mul_cpow_ofReal_nonneg
        (le_of_lt (lt_trans zero_lt_one positiveU)) (le_of_lt positiveX)]
    have xNe : (x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr positiveX.ne'
    have exponentZero : (2 * z) + (-2 * z) = 0 := by ring
    calc
      (u : ℂ) ^ (-2 * z) * value (u * x) =
          1 * ((u : ℂ) ^ (-2 * z) * value (u * x)) := by rw [one_mul]
      _ = ((x : ℂ) ^ (2 * z) * (x : ℂ) ^ (-2 * z)) *
          ((u : ℂ) ^ (-2 * z) * value (u * x)) := by
        rw [← Complex.cpow_add _ _ xNe, exponentZero, Complex.cpow_zero]
      _ = _ := by ring
  calc
    _ = ∫ u : ℝ in Ioi (1 : ℝ),
        (x : ℂ) ^ (2 * z) * weighted (u * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact integrandEq
    _ = (x : ℂ) ^ (2 * z) *
        ∫ u : ℝ in Ioi (1 : ℝ), weighted (u * x) := by
      rw [integral_const_mul]
    _ = (x : ℂ) ^ (2 * z) *
        ((x : ℝ)⁻¹ • ∫ t : ℝ in Ioi (1 * x), weighted t) := by rw [change]
    _ = _ := by
      simp only [one_mul, weighted, Complex.real_smul]
      rw [Complex.ofReal_inv,
        show (x : ℂ)⁻¹ = (x : ℂ) ^ (-(1 : ℂ)) by
          rw [Complex.cpow_neg, Complex.cpow_one]]
      rw [← mul_assoc, ← Complex.cpow_add _ _
        (Complex.ofReal_ne_zero.mpr positiveX.ne')]
      congr 2

theorem burnolFourierRightDivisionRaw_eq_tail
    (z : ℂ) (value : ℝ → ℂ) {x : ℝ} (positiveX : 0 < x) :
    burnolFourierRightDivisionRaw z value x =
      -2 * (x : ℂ) ^ (2 * z - 1) *
        ∫ t : ℝ in Ioi x, (t : ℂ) ^ (-2 * z) * value t := by
  rw [burnolFourierRightDivisionRaw_exp_change,
    burnolFourierRightDivision_tail_change z value positiveX]
  ring

theorem integral_cpow_neg_on_positiveIoc
    (lower upper : ℝ) (_positiveLower : 0 < lower) (bounded : lower ≤ upper)
    (coordinate : ℂ) (belowOne : coordinate.re < 1) :
    (∫ t : ℝ in Ioc lower upper, (t : ℂ) ^ (-coordinate)) =
      burnolRadiusMellinGapMoment upper coordinate -
        burnolRadiusMellinGapMoment lower coordinate := by
  have exponent : -1 < (-coordinate).re := by
    simp only [neg_re]
    linarith
  rw [← intervalIntegral.integral_of_le bounded,
    integral_cpow (Or.inl exponent)]
  unfold burnolRadiusMellinGapMoment
  have exponentEq : -coordinate + 1 = 1 - coordinate := by ring
  rw [exponentEq]
  ring

theorem physicalValue_ae_eq_gapCoefficient_on_Ioc
    (radius : ℝ) (positive : 0 < radius)
    (value : EvenBurnolPhysicalCarrier radius) (coefficient : ℂ)
    (gap : coefficient • intervalConstant radius =
      restrictToInterval radius (value : BurnolL2)) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 radius),
      (value : BurnolL2) x = coefficient := by
  have onSymmetric : ∀ᵐ x ∂volume.restrict (symmetricInterval radius),
      (value : BurnolL2) x = coefficient := by
    filter_upwards [Lp.coeFn_smul coefficient (intervalConstant radius),
      intervalConstant_coeFn radius,
      LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius)
        (value : BurnolL2)] with x hsmul hconstant hrestrict
    calc
      (value : BurnolL2) x =
          restrictToInterval radius (value : BurnolL2) x := hrestrict.symm
      _ = (coefficient • intervalConstant radius) x := by rw [← gap]
      _ = coefficient * intervalConstant radius x := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
      _ = coefficient := by rw [hconstant, mul_one]
  apply ae_restrict_of_ae_restrict_of_subset _ onSymmetric
  intro x hx
  change -radius ≤ x ∧ x ≤ radius
  exact ⟨by linarith [hx.1, positive], hx.2⟩

theorem physicalValue_mellin_integrableOn_Ioc
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier radius) (coefficient : ℂ)
    (gap : coefficient • intervalConstant radius =
      restrictToInterval radius (value : BurnolL2)) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x)
      (Ioc 0 radius) := by
  have exponent : -1 < (-coordinate.value).re := by
    simp only [neg_re]
    linarith [coordinate.belowOne]
  have powerIntegrable : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-coordinate.value)) (Ioc 0 radius) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le positive.le).mp
      (intervalIntegral.intervalIntegrable_cpow' exponent)
  apply (powerIntegrable.mul_const coefficient).congr
  filter_upwards [physicalValue_ae_eq_gapCoefficient_on_Ioc
    radius positive value coefficient gap] with x valueRead
  rw [valueRead]

/-- The state-owned completed-Mellin zero makes the Fourier-side tail at
every positive point of the gap equal to the negative local Mellin moment.
This is the cancellation used by division; it is read from `value` itself. -/
theorem burnolCompletedMellin_zero_tail_eq
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier radius)
    (readZero :
      burnolRadiusCompletedMellinEvaluator radius positive coordinate value = 0) :
    ∃ coefficient : ℂ,
      coefficient • intervalConstant radius =
          restrictToInterval radius (value : BurnolL2) ∧
      ∀ t : ℝ, 0 < t → t ≤ radius →
        (∫ u : ℝ in Ioi t,
          (u : ℂ) ^ (-coordinate.value) * (value : BurnolL2) u) =
        -burnolRadiusMellinGapMoment t coordinate.value * coefficient := by
  obtain ⟨coefficient, gap⟩ :=
    mem_locallyConstantFace_iff_exists.mp value.property.1.1
  refine ⟨coefficient, gap, ?_⟩
  intro t positiveT bounded
  have localIntegrable := physicalValue_mellin_integrableOn_Ioc
    radius positive coordinate value coefficient gap
  have tailIntegrable := burnolRadiusMellinWeight_integrableOn_tail
    radius positive coordinate.value coordinate.rightHalf (value : BurnolL2)
  have middleIntegrable : IntegrableOn (fun u : ℝ =>
      (u : ℂ) ^ (-coordinate.value) * (value : BurnolL2) u) (Ioc t radius) :=
    localIntegrable.mono_set (by
      intro u hu
      exact ⟨lt_trans positiveT hu.1, hu.2⟩)
  have split : Ioc t radius ∪ Ioi radius = Ioi t :=
    Ioc_union_Ioi_eq_Ioi bounded
  have disjoint : Disjoint (Ioc t radius) (Ioi radius) := by
    rw [Set.disjoint_left]
    intro u first second
    exact (not_lt_of_ge first.2) second
  have readExpanded :
      burnolRadiusMellinGapMoment radius coordinate.value * coefficient +
        (∫ u : ℝ in Ioi radius,
          (u : ℂ) ^ (-coordinate.value) * (value : BurnolL2) u) = 0 := by
    simpa only [burnolRadiusCompletedMellinEvaluator, add_apply, smul_apply,
      smul_eq_mul, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      burnolRadiusMellinTailEvaluator_eq_integral,
      burnolConstantGapCoefficient_eq radius positive value coefficient gap]
      using readZero
  have middleRead :
      (∫ u : ℝ in Ioc t radius,
        (u : ℂ) ^ (-coordinate.value) * (value : BurnolL2) u) =
      (burnolRadiusMellinGapMoment radius coordinate.value -
          burnolRadiusMellinGapMoment t coordinate.value) * coefficient := by
    calc
      _ = ∫ u : ℝ in Ioc t radius,
          (u : ℂ) ^ (-coordinate.value) * coefficient := by
        apply integral_congr_ae
        have localRead := physicalValue_ae_eq_gapCoefficient_on_Ioc
          radius positive value coefficient gap
        have middleRead : ∀ᵐ u ∂volume.restrict (Ioc t radius),
            (value : BurnolL2) u = coefficient :=
          ae_restrict_of_ae_restrict_of_subset
            (by
              intro u hu
              exact ⟨lt_trans positiveT hu.1, hu.2⟩)
            localRead
        filter_upwards [middleRead] with u valueRead
        rw [valueRead]
      _ = (∫ u : ℝ in Ioc t radius,
          (u : ℂ) ^ (-coordinate.value)) * coefficient := by
        rw [integral_mul_const]
      _ = _ := by
        rw [integral_cpow_neg_on_positiveIoc t radius positiveT bounded
          coordinate.value coordinate.belowOne]
  calc
    (∫ u : ℝ in Ioi t,
        (u : ℂ) ^ (-coordinate.value) * (value : BurnolL2) u) =
      (∫ u : ℝ in Ioc t radius,
          (u : ℂ) ^ (-coordinate.value) * (value : BurnolL2) u) +
        ∫ u : ℝ in Ioi radius,
          (u : ℂ) ^ (-coordinate.value) * (value : BurnolL2) u := by
      rw [← setIntegral_union disjoint measurableSet_Ioi
        middleIntegrable tailIntegrable, split]
    _ = _ := by rw [middleRead]; linear_combination readExpanded

/-- Burnol's Fourier-side division formula is constant throughout the
positive gap once its completed-Mellin read vanishes. -/
theorem burnolFourierRightResolventTail_constant_on_positiveGap
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier radius)
    (readZero :
      burnolRadiusCompletedMellinEvaluator radius positive coordinate value = 0) :
    ∃ coefficient : ℂ,
      coefficient • intervalConstant radius =
          restrictToInterval radius (value : BurnolL2) ∧
      ∀ t : ℝ, 0 < t → t ≤ radius →
        (-2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
            (∫ u : ℝ in Ioi t,
              (u : ℂ) ^ (-coordinate.value) * (value : BurnolL2) u) =
          (2 : ℂ) * coefficient / (1 - coordinate.value) := by
  obtain ⟨coefficient, gap, tail⟩ :=
    burnolCompletedMellin_zero_tail_eq
      radius positive coordinate value readZero
  refine ⟨coefficient, gap, ?_⟩
  intro t positiveT bounded
  rw [tail t positiveT bounded]
  unfold burnolRadiusMellinGapMoment
  have tNe : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt positiveT
  have denominatorNe : 1 - coordinate.value ≠ 0 := by
    intro zero
    have : coordinate.value = 1 := (sub_eq_zero.mp zero).symm
    have below := coordinate.belowOne
    rw [this] at below
    norm_num at below
  have powers :
      (t : ℂ) ^ (coordinate.value - 1) *
          (t : ℂ) ^ (1 - coordinate.value) = 1 := by
    rw [← Complex.cpow_add _ _ tNe]
    convert Complex.cpow_zero (t : ℂ) using 2
    all_goals ring
  rw [neg_mul]
  field_simp [denominatorNe]
  rw [powers]
  ring

/-- The logarithmic expanding-dilation integral itself has the exact gap
constant forced by the state-owned completed-Mellin zero. -/
theorem burnolFourierRightDivisionRaw_eq_gapConstant
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate)
    (value : EvenBurnolPhysicalCarrier radius)
    (readZero :
      burnolRadiusCompletedMellinEvaluator radius positive coordinate value = 0)
    {x : ℝ} (positiveX : 0 < x) (bounded : x ≤ radius) :
    burnolFourierRightDivisionRaw (coordinate.value / 2)
        (value : BurnolL2) x =
      (2 : ℂ) * burnolConstantGapCoefficient radius value /
        (1 - coordinate.value) := by
  obtain ⟨coefficient, gap, constant⟩ :=
    burnolFourierRightResolventTail_constant_on_positiveGap
      radius positive coordinate value readZero
  rw [burnolFourierRightDivisionRaw_eq_tail _ _ positiveX]
  have doubled : 2 * (coordinate.value / 2) = coordinate.value := by ring
  have negDoubled : -2 * (coordinate.value / 2) = -coordinate.value := by ring
  rw [doubled, negDoubled]
  rw [constant x positiveX bounded]
  rw [burnolConstantGapCoefficient_eq radius positive value coefficient gap]

/-! ## Hilbert/Fubini bridge on the canonical Burnol radius -/

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
