import H0mework.Versions.V2.Arithmetic.BurnolMellin.CompletedMellinPrimaryGenerator

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

theorem burnolGenericPhysicalValue_gap
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value •
        intervalConstant burnolUnscaledCommonGapRadius =
      restrictToInterval burnolUnscaledCommonGapRadius (value : BurnolL2) := by
  obtain ⟨coefficient, gap⟩ :=
    (mem_locallyConstantFace_iff_exists.mp value.property.1.1)
  have coefficientRead := burnolConstantGapCoefficient_eq
    burnolUnscaledCommonGapRadius
    (by norm_num [burnolUnscaledCommonGapRadius]) value coefficient gap
  rw [coefficientRead]
  exact gap

theorem burnolGenericPhysicalValue_ae_eq_gapCoefficient_on_Ioc
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 burnolUnscaledCommonGapRadius),
      (value : BurnolL2) x =
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
  let coefficient :=
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value
  have gap := burnolGenericPhysicalValue_gap value
  have onSymmetric : ∀ᵐ x ∂volume.restrict
      (symmetricInterval burnolUnscaledCommonGapRadius),
      (value : BurnolL2) x = coefficient := by
    filter_upwards [Lp.coeFn_smul coefficient
        (intervalConstant burnolUnscaledCommonGapRadius),
      intervalConstant_coeFn burnolUnscaledCommonGapRadius,
      LpToLpRestrictCLM_coeFn ℂ
        (symmetricInterval burnolUnscaledCommonGapRadius) (value : BurnolL2)]
      with x hsmul hconstant hrestrict
    calc
      (value : BurnolL2) x =
          restrictToInterval burnolUnscaledCommonGapRadius
            (value : BurnolL2) x := hrestrict.symm
      _ = (coefficient • intervalConstant burnolUnscaledCommonGapRadius) x :=
        congrArg (fun f => f x) gap.symm
      _ = coefficient * intervalConstant burnolUnscaledCommonGapRadius x := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
      _ = coefficient := by rw [hconstant, mul_one]
  apply ae_restrict_of_ae_restrict_of_subset _ onSymmetric
  intro x hx
  change -burnolUnscaledCommonGapRadius ≤ x ∧
    x ≤ burnolUnscaledCommonGapRadius
  exact ⟨by
    have positiveRadius : 0 < burnolUnscaledCommonGapRadius := by
      norm_num [burnolUnscaledCommonGapRadius]
    linarith [hx.1], hx.2⟩

theorem burnolGenericPhysicalMellin_integrableOn_gap
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x)
      (Ioc 0 burnolUnscaledCommonGapRadius) := by
  have exponent : -1 < (-coordinate.value).re := by
    simp only [neg_re]
    linarith [coordinate.belowOne]
  have powerIntegrable : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-coordinate.value))
      (Ioc 0 burnolUnscaledCommonGapRadius) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ burnolUnscaledCommonGapRadius by
        norm_num [burnolUnscaledCommonGapRadius])).mp
      (intervalIntegral.intervalIntegrable_cpow' exponent)
  apply (powerIntegrable.mul_const
    (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value)).congr
  filter_upwards [burnolGenericPhysicalValue_ae_eq_gapCoefficient_on_Ioc value]
    with x valueRead
  rw [valueRead]

theorem burnolGenericPhysicalMellin_integrableOn_tail
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x)
      (Ioi burnolUnscaledCommonGapRadius) :=
  burnolMellinWeight_integrableOn_tail coordinate.value
    coordinate.rightHalf (value : BurnolL2)

theorem burnolGenericPhysicalMellin_integrableOn_positive
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi
    (show (0 : ℝ) ≤ burnolUnscaledCommonGapRadius by
      norm_num [burnolUnscaledCommonGapRadius])]
  exact (burnolGenericPhysicalMellin_integrableOn_gap value coordinate).union
    (burnolGenericPhysicalMellin_integrableOn_tail value coordinate)

theorem burnolGenericPhysicalMellin_gap_integral
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in Ioc 0 burnolUnscaledCommonGapRadius,
      (x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x) =
      burnolMellinGapMoment coordinate.value *
        burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
  calc
    _ = ∫ x : ℝ in Ioc 0 burnolUnscaledCommonGapRadius,
        (x : ℂ) ^ (-coordinate.value) *
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
      apply integral_congr_ae
      filter_upwards [burnolGenericPhysicalValue_ae_eq_gapCoefficient_on_Ioc
        value] with x valueRead
      rw [valueRead]
    _ = (∫ x : ℝ in Ioc 0 burnolUnscaledCommonGapRadius,
        (x : ℂ) ^ (-coordinate.value)) *
          burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value := by
      rw [integral_mul_const]
    _ = _ := by
      rw [integral_cpow_neg_on_burnolGap coordinate.value coordinate.belowOne]

/-- Every admitted physical vector has an honest positive completed-Mellin
read.  The gap coefficient supplies the missing finite interval and the tail
is the existing `L²` continuous evaluator. -/
theorem burnolCompletedMellinEvaluator_eq_positive_integral
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompletedMellinEvaluator coordinate value =
      ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x := by
  have gapIntegrable :=
    burnolGenericPhysicalMellin_integrableOn_gap value coordinate
  have tailIntegrable :=
    burnolGenericPhysicalMellin_integrableOn_tail value coordinate
  have disjoint : Disjoint
      (Ioc (0 : ℝ) burnolUnscaledCommonGapRadius)
      (Ioi burnolUnscaledCommonGapRadius) := by
    rw [Set.disjoint_left]
    intro x first second
    exact (not_lt_of_ge first.2) second
  rw [burnolCompletedMellinEvaluator_apply,
    burnolMellinTailEvaluator_eq_integral]
  simp only [smul_eq_mul]
  rw [← Ioc_union_Ioi_eq_Ioi
      (show (0 : ℝ) ≤ burnolUnscaledCommonGapRadius by
        norm_num [burnolUnscaledCommonGapRadius]),
    setIntegral_union disjoint measurableSet_Ioi gapIntegrable tailIntegrable,
    burnolGenericPhysicalMellin_gap_integral]

theorem burnolCompletedMellinRieszVector_generic_readback
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate) value =
      ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-coordinate.value) * (value : BurnolL2) x := by
  rw [burnolCompletedMellinRieszVector_readback,
    burnolCompletedMellinEvaluator_eq_positive_integral]

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
