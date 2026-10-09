import H0mework.Arithmetic.BurnolMellin.CompletedMellinEvaluatorKernel
import H0mework.Arithmetic.Muntz.CoPoissonMuntzFactorization
import H0mework.Versions.R2.Arithmetic.RiemannSource.NontrivialCompletedZero

/-! # Completed-Mellin readback on primary Burnol co-Poisson generators -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

theorem burnolCompactAdditivePhysicalState_gap
    (source : burnolCompactAnnulusSource) :
    (-burnolCompactAdditiveNormalization source) •
        intervalConstant burnolUnscaledCommonGapRadius =
      restrictToInterval burnolUnscaledCommonGapRadius
        ((burnolCompactAdditivePhysicalState source :
          EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) : BurnolL2) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul
      (-burnolCompactAdditiveNormalization source)
      (intervalConstant burnolUnscaledCommonGapRadius),
    intervalConstant_coeFn burnolUnscaledCommonGapRadius,
    LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval burnolUnscaledCommonGapRadius)
      (burnolCompactAdditiveL2 source),
    ae_restrict_of_ae (burnolCompactAdditiveL2_coeFn source),
    ae_restrict_mem (measurableSet_symmetricInterval
      burnolUnscaledCommonGapRadius)] with t hsmul hconst hrestrict hvalue ht
  calc
    ((-burnolCompactAdditiveNormalization source) •
        intervalConstant burnolUnscaledCommonGapRadius :
          Lp ℂ 2 (volume.restrict
            (symmetricInterval burnolUnscaledCommonGapRadius))) t =
      -burnolCompactAdditiveNormalization source *
        intervalConstant burnolUnscaledCommonGapRadius t := by
          simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
    _ = -burnolCompactAdditiveNormalization source := by
      rw [hconst, mul_one]
    _ = burnolCompactAdditiveCoSum source t := by
      symm
      apply burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
      exact (abs_le).2 (by
        simpa [symmetricInterval, burnolUnscaledCommonGapRadius] using ht)
    _ = burnolCompactAdditiveL2 source t := hvalue.symm
    _ = restrictToInterval burnolUnscaledCommonGapRadius
        (burnolCompactAdditiveL2 source) t := hrestrict.symm

theorem burnolConstantGapCoefficient_compactAdditivePhysicalState
    (source : burnolCompactAnnulusSource) :
    burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
        (burnolCompactAdditivePhysicalState source) =
      -burnolCompactAdditiveNormalization source := by
  apply burnolConstantGapCoefficient_eq
    burnolUnscaledCommonGapRadius
      (by norm_num [burnolUnscaledCommonGapRadius])
  exact burnolCompactAdditivePhysicalState_gap source

theorem integral_cpow_neg_on_burnolGap
    (coordinate : ℂ) (belowOne : coordinate.re < 1) :
    ∫ t : ℝ in Ioc 0 burnolUnscaledCommonGapRadius,
        (t : ℂ) ^ (-coordinate) =
      burnolMellinGapMoment coordinate := by
  have exponent : -1 < (-coordinate).re := by
    simp only [neg_re]
    linarith
  have denominatorNe : 1 - coordinate ≠ 0 := by
    intro zero
    have : coordinate = 1 := (sub_eq_zero.mp zero).symm
    subst coordinate
    norm_num at belowOne
  rw [← intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ burnolUnscaledCommonGapRadius by
        norm_num [burnolUnscaledCommonGapRadius]),
    integral_cpow (Or.inl exponent)]
  unfold burnolMellinGapMoment burnolRadiusMellinGapMoment
  have exponentEq : -coordinate + 1 = 1 - coordinate := by ring
  rw [exponentEq, Complex.ofReal_zero, zero_cpow denominatorNe, sub_zero]

theorem burnolCompactAdditiveMellin_integrableOn_gap
    (source : burnolCompactAnnulusSource) (coordinate : ℂ)
    (belowOne : coordinate.re < 1) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (-coordinate) * burnolCompactAdditiveCoSum source t)
      (Ioc 0 burnolUnscaledCommonGapRadius) := by
  have exponent : -1 < (-coordinate).re := by
    simp only [neg_re]
    linarith
  have powerIntegrable : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-coordinate))
      (Ioc 0 burnolUnscaledCommonGapRadius) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ burnolUnscaledCommonGapRadius by
        norm_num [burnolUnscaledCommonGapRadius])).mp
      (intervalIntegral.intervalIntegrable_cpow' exponent)
  apply (powerIntegrable.mul_const
    (-burnolCompactAdditiveNormalization source)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  congr 1
  rw [burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter]
  have nonnegative : 0 ≤ t := ht.1.le
  rw [abs_of_nonneg nonnegative]
  exact ht.2

theorem burnolCompactAdditiveMellin_integrableOn_tail
    (source : burnolCompactAnnulusSource) (coordinate : ℂ)
    (rightHalf : 1 / 2 < coordinate.re) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (-coordinate) * burnolCompactAdditiveCoSum source t)
      (Ioi burnolUnscaledCommonGapRadius) := by
  apply (burnolMellinWeight_integrableOn_tail coordinate rightHalf
    (burnolCompactAdditiveL2 source)).congr
  filter_upwards [ae_restrict_of_ae
    (burnolCompactAdditiveL2_coeFn source)] with t valueRead
  rw [valueRead]

def burnolCompactAdditiveMellinRead
    (source : burnolCompactAnnulusSource) (coordinate : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    (t : ℂ) ^ (-coordinate) * burnolCompactAdditiveCoSum source t

theorem two_mul_burnolCompactAdditiveMellinRead_eq_mellin
    (source : burnolCompactAnnulusSource) (coordinate : ℂ) :
    2 * burnolCompactAdditiveMellinRead source coordinate =
      mellin (coPoissonMuntzScaleRemainder source.1) coordinate := by
  calc
    _ = mellin (fun t =>
        coPoissonMuntzScaleRemainder source.1 t⁻¹) (-coordinate) := by
      unfold burnolCompactAdditiveMellinRead mellin
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
      rw [coPoissonMuntzScaleRemainder_reciprocal_eq_compactAdditiveCoSum
        source positive]
      simp only [smul_eq_mul]
      push_cast
      symm
      calc
        (t : ℂ) ^ (-coordinate - 1) *
            (2 * (t : ℂ) * burnolCompactAdditiveCoSum source t) =
          2 * ((t : ℂ) ^ (-coordinate - 1) * (t : ℂ)) *
            burnolCompactAdditiveCoSum source t := by ring
        _ = 2 * ((t : ℂ) ^ (-coordinate - 1) * (t : ℂ) ^ (1 : ℂ)) *
            burnolCompactAdditiveCoSum source t := by rw [Complex.cpow_one]
        _ = 2 * (t : ℂ) ^ ((-coordinate - 1) + 1) *
            burnolCompactAdditiveCoSum source t := by
              rw [Complex.cpow_add _ _
                (Complex.ofReal_ne_zero.mpr positive.ne')]
        _ = 2 * (t : ℂ) ^ (-coordinate) *
            burnolCompactAdditiveCoSum source t := by
              have exponentEq : (-coordinate - 1) + 1 = -coordinate := by ring
              rw [exponentEq]
        _ = 2 * ((t : ℂ) ^ (-coordinate) *
            burnolCompactAdditiveCoSum source t) := by ring
    _ = _ := by
      simpa only [neg_neg] using
        mellin_comp_inv (coPoissonMuntzScaleRemainder source.1) (-coordinate)

theorem burnolCompletedMellinEvaluator_compactAdditivePhysicalState
    (source : burnolCompactAnnulusSource)
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompletedMellinEvaluator coordinate
        (burnolCompactAdditivePhysicalState source) =
      burnolCompactAdditiveMellinRead source coordinate.value := by
  have gapIntegrable := burnolCompactAdditiveMellin_integrableOn_gap
    source coordinate.value coordinate.belowOne
  have tailIntegrable := burnolCompactAdditiveMellin_integrableOn_tail
    source coordinate.value coordinate.rightHalf
  have disjoint : Disjoint
      (Ioc (0 : ℝ) burnolUnscaledCommonGapRadius)
      (Ioi burnolUnscaledCommonGapRadius) := by
    rw [Set.disjoint_left]
    intro t first second
    exact (not_lt_of_ge first.2) second
  have gapIntegral :
      (∫ t : ℝ in Ioc 0 burnolUnscaledCommonGapRadius,
        (t : ℂ) ^ (-coordinate.value) *
          burnolCompactAdditiveCoSum source t) =
        burnolMellinGapMoment coordinate.value *
          (-burnolCompactAdditiveNormalization source) := by
    calc
      _ = ∫ t : ℝ in Ioc 0 burnolUnscaledCommonGapRadius,
          (t : ℂ) ^ (-coordinate.value) *
            (-burnolCompactAdditiveNormalization source) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        change (t : ℂ) ^ (-coordinate.value) *
            burnolCompactAdditiveCoSum source t = _
        rw [burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter]
        have nonnegative : 0 ≤ t := ht.1.le
        rw [abs_of_nonneg nonnegative]
        exact ht.2
      _ = (∫ t : ℝ in Ioc 0 burnolUnscaledCommonGapRadius,
          (t : ℂ) ^ (-coordinate.value)) *
            (-burnolCompactAdditiveNormalization source) := by
        exact integral_mul_const _ _
      _ = _ := by
        rw [integral_cpow_neg_on_burnolGap coordinate.value coordinate.belowOne]
  rw [burnolCompletedMellinEvaluator_apply,
    burnolConstantGapCoefficient_compactAdditivePhysicalState,
    burnolMellinTailEvaluator_eq_integral]
  change burnolMellinGapMoment coordinate.value •
        (-burnolCompactAdditiveNormalization source) +
      (∫ t : ℝ in Ioi burnolUnscaledCommonGapRadius,
        (t : ℂ) ^ (-coordinate.value) * burnolCompactAdditiveL2 source t) = _
  have tailRead :
      (∫ t : ℝ in Ioi burnolUnscaledCommonGapRadius,
        (t : ℂ) ^ (-coordinate.value) * burnolCompactAdditiveL2 source t) =
      ∫ t : ℝ in Ioi burnolUnscaledCommonGapRadius,
        (t : ℂ) ^ (-coordinate.value) * burnolCompactAdditiveCoSum source t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae
      (burnolCompactAdditiveL2_coeFn source)] with t valueRead
    rw [valueRead]
  rw [tailRead]
  simp only [smul_eq_mul]
  unfold burnolCompactAdditiveMellinRead
  rw [← Set.Ioc_union_Ioi_eq_Ioi
      (show (0 : ℝ) ≤ burnolUnscaledCommonGapRadius by
        norm_num [burnolUnscaledCommonGapRadius]),
    setIntegral_union disjoint measurableSet_Ioi gapIntegrable tailIntegrable,
    gapIntegral]

theorem four_mul_burnolCompletedMellinEvaluator_eq_quarterMellinRead
    (source : burnolCompactAnnulusSource)
    (coordinate : BurnolCompletedMellinCoordinate) :
    4 * burnolCompletedMellinEvaluator coordinate
        (burnolCompactAdditivePhysicalState source) =
      quarterMellinL2Functional (coordinate.value / 2)
        (coPoissonQuarterMellinConvergentMap
          (coordinate.value / 2)
          (by rw [Complex.div_re]; norm_num; linarith [coordinate.rightHalf])
          (by rw [Complex.div_re]; norm_num; linarith [coordinate.belowOne])
          source.1) := by
  rw [burnolCompletedMellinEvaluator_compactAdditivePhysicalState
    source coordinate]
  change 4 * burnolCompactAdditiveMellinRead source coordinate.value =
    mellin (positiveMellinExtension (coPoissonQuarterMellinMap source.1))
      (coordinate.value / 2)
  rw [positiveMellinExtension_coPoissonQuarterMellinMap_mellin_eq]
  have relation := two_mul_burnolCompactAdditiveMellinRead_eq_mellin
    source coordinate.value
  rw [show (2 : ℂ) * (coordinate.value / 2) = coordinate.value by ring,
    ← relation]
  ring

theorem burnolCompletedMellinEvaluator_compactAdditivePhysicalState_eq_zero
    (source : burnolCompactAnnulusSource)
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolCompletedMellinEvaluator coordinate
        (burnolCompactAdditivePhysicalState source) = 0 := by
  have quarterZero :
      quarterMellinL2Functional (coordinate.value / 2)
        (coPoissonQuarterMellinConvergentMap
          (coordinate.value / 2)
          (by rw [Complex.div_re]; norm_num; linarith [coordinate.rightHalf])
          (by rw [Complex.div_re]; norm_num; linarith [coordinate.belowOne])
          source.1) = 0 := by
    rw [quarterMellinL2Functional_coPoissonQuarterMellinConvergentMap,
      show (2 : ℂ) * (coordinate.value / 2) = coordinate.value by ring,
      zero, zero_mul]
  have bridge := four_mul_burnolCompletedMellinEvaluator_eq_quarterMellinRead
    source coordinate
  rw [quarterZero] at bridge
  exact (mul_eq_zero.mp bridge).resolve_left (by norm_num)

theorem burnolCompletedMellinEvaluator_primaryGenerator_eq_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (source : burnolCompactAnnulusSource) :
    burnolCompletedMellinEvaluator coordinate
        (burnolCompactCoPoissonGenerator (source, 0)) = 0 := by
  change burnolCompletedMellinEvaluator coordinate
      (burnolCompactAdditivePhysicalState source) = 0
  exact burnolCompletedMellinEvaluator_compactAdditivePhysicalState_eq_zero
    source coordinate zero

theorem selectedRightHalfZero_burnolPrimaryGenerator_orthogonal
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) :
    inner ℂ
        (burnolCompletedMellinRieszVector
          ⟨observation.coordinate, rightHalf, observation.coordinate_re_lt_one⟩)
        (burnolCompactCoPoissonGenerator (source, 0)) = 0 := by
  rw [burnolCompletedMellinRieszVector_readback]
  exact burnolCompletedMellinEvaluator_primaryGenerator_eq_zero
    ⟨observation.coordinate, rightHalf, observation.coordinate_re_lt_one⟩
      observation.mathlibZero source

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
