import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.BVolterra
import H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorWindowHAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalKExteriorCoPoissonAction OriginalKExteriorRVolterra OriginalKExteriorBRVolterra
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology
local notation "q" => (1 / 4 : ℝ)
local instance quarterFinite : IsFiniteMeasure ((volume : Measure ℝ).restrict (symmetricInterval q)) where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def sourceForce (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![bForce c, returnForce c]
def sourceDerivative (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![sourceRawDerivative c, burnolRieszReturnRawDerivative c]
def sourceExponent (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℂ :=
  ![1 - star c.value, star c.value]
def sourceHRate (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : ℂ :=
  sourceExponent c i - 1 / 2

def physicalTest (c : BurnolCompletedMellinCoordinate) : Fin 2 → BurnolL2 :=
  ![fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2),
    (burnolCompletedMellinRieszVector c : BurnolL2)]
def canonicalTestRaw (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![burnolRieszFourierRaw c, burnolRieszStateRaw c]
def exteriorTestRaw (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![burnolRieszFourierExteriorRaw c, burnolRieszStatePositiveOuterRaw c]

theorem physical_test_ae_raw (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (physicalTest c i : ℝ → ℂ) =ᵐ[volume] canonicalTestRaw c i := by
  fin_cases i
  · exact burnolRieszFourier_ae_raw c
  · exact burnolRieszState_ae_raw c

theorem physical_test_raw_outer (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ)
    (outside : q < |x|) : canonicalTestRaw c i x = exteriorTestRaw c i |x| := by
  by_cases positive : 0 ≤ x
  · rw [abs_of_nonneg positive] at outside ⊢
    fin_cases i
    · exact fourier_raw_eq_exterior c outside
    · exact burnolRieszStateRaw_eq_positiveOuter c outside
  · have negative : x < 0 := lt_of_not_ge positive
    rw [abs_of_neg negative] at outside ⊢
    fin_cases i
    · exact (fourier_raw_even c x).symm.trans (fourier_raw_eq_exterior c outside)
    · exact (burnolRieszStateRaw_even c x).symm.trans (burnolRieszStateRaw_eq_positiveOuter c outside)

theorem physical_test_outer_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0 < x) : ContinuousAt (exteriorTestRaw c i) x := by
  fin_cases i
  · exact burnolRieszFourierExteriorRaw_continuousAt c positive.ne'
  · change ContinuousAt (burnolRieszStatePositiveOuterRaw c) x
    rw [funext (position_exterior_return_read c)]
    exact ((Complex.continuousAt_ofReal_cpow_const x (-star c.value) (Or.inr positive.ne')).const_mul _).sub
      ((burnolRieszReturnRaw_continuous c).continuousAt.add continuousAt_const)

private theorem complex_integral_comp_abs (f : ℝ → ℂ) :
    (∫ x : ℝ, f |x|) = 2 * ∫ x : ℝ in Ioi 0, f x := by
  have equal : (∫ x : ℝ in Ioi 0, f |x|) = ∫ x : ℝ in Ioi 0, f x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x positive
    change f |x| = f x
    rw [abs_of_pos (show 0 < x from positive)]
  by_cases integrable : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have negative : IntegrableOn (fun x => f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let embedding : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
      rw [embedding.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi integrable
    calc
      _ = (∫ x : ℝ in Iic 0, f |x|) + ∫ x : ℝ in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi negative integrable,
          Iic_union_Ioi, Measure.restrict_univ]
      _ = _ := by
        rw [two_mul, equal]
        congr 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        apply setIntegral_congr_fun measurableSet_Iic
        intro x nonpositive
        change f |x| = f (-x)
        rw [abs_of_nonpos (show x ≤ 0 from nonpositive)]
  · have global : ¬Integrable (fun x => f |x|) := fun total => integrable total.integrableOn
    rw [← equal, integral_undef integrable, integral_undef global, mul_zero]

def exteriorPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : ℂ :=
  2 * (Real.exp (-h / 2) : ℂ) *
    ∫ x : ℝ in q..(q * Real.exp h),
      star (exteriorTestRaw c i x) * sourceProfile c i (Real.exp (-h) * x)

theorem actual_exterior_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    inner ℂ (physicalTest c i) (exteriorSource c h i) = exteriorPrice c h i := by
  rw [L2.inner_def]
  let density : ℝ → ℂ := fun x => star (exteriorTestRaw c i x) *
    ((Real.exp (-h / 2) : ℂ) * sourceProfile c i (Real.exp (-h) * x))
  have actual : (fun x : ℝ => inner ℂ (physicalTest c i x) (exteriorSource c h i x)) =ᵐ[volume]
      (fun x => (Ioc q (q * Real.exp h)).indicator density |x|) := by
    filter_upwards [physical_test_ae_raw c i, actual_source_raw c h nonnegative i] with x test source
    rw [source]
    unfold shellRaw
    by_cases active : q < |x| ∧ |x| ≤ q * Real.exp h
    · rw [if_pos active, indicator_of_mem (show |x| ∈ Ioc q (q * Real.exp h) from active),
        test, physical_test_raw_outer c i x active.1]
      simp only [RCLike.inner_apply, density, starRingEnd_apply]
      ring
    · rw [if_neg active,
        indicator_of_notMem (show |x| ∉ Ioc q (q * Real.exp h) from active), inner_zero_right]
  rw [integral_congr_ae actual, complex_integral_comp_abs,
    integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have intersection : Ioc q (q * Real.exp h) ∩ Ioi 0 = Ioc q (q * Real.exp h) := by
    apply inter_eq_left.mpr
    intro x inside
    exact lt_trans (by norm_num) inside.1
  rw [intersection]
  have ordered : q ≤ q * Real.exp h := by
    have scale := Real.one_le_exp_iff.mpr nonnegative
    nlinarith
  rw [← intervalIntegral.integral_of_le ordered]
  have factor : density = fun x => (Real.exp (-h / 2) : ℂ) *
      (star (exteriorTestRaw c i x) * sourceProfile c i (Real.exp (-h) * x)) := by
    funext x
    dsimp only [density]
    ring
  rw [factor, intervalIntegral.integral_const_mul]
  exact (mul_assoc _ _ _).symm

theorem actual_full_loss_cotest (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    inner ℂ (physicalTest c i) (FullUnit.fullSource c h i) =
      exteriorPrice c h i + centeringMean c h i * inner ℂ (physicalTest c i) ConstantDual.seed := by
  rw [FullUnit.full_source_inventory c h nonnegative i, inner_add_right, inner_smul_right,
    actual_exterior_cotest c h nonnegative i]

private theorem profile_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0 < x) : HasDerivAt (sourceProfile c i) (sourceDerivative c i x) x := by
  fin_cases i
  · exact sourceRaw_hasDerivAt c x positive.ne'
  · exact burnolRieszReturnRaw_hasDerivAt c x

private theorem actual_profile_ODE (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0 < x) (bounded : x ≤ q) :
    (x : ℂ) * sourceDerivative c i x + sourceExponent c i * sourceProfile c i x = sourceForce c i x := by
  fin_cases i
  · exact actual_b_source_ODE c x positive bounded
  · exact actual_return_source_ODE c x

theorem actual_profile_h_action (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (h x : ℝ) (positive : 0 < x) (bounded : x ≤ q * Real.exp h) :
    HasDerivAt (fun s : ℝ => (Real.exp (-s / 2) : ℂ) * sourceProfile c i (Real.exp (-s) * x))
      (sourceHRate c i * ((Real.exp (-h / 2) : ℂ) * sourceProfile c i (Real.exp (-h) * x)) -
        (Real.exp (-h / 2) : ℂ) * sourceForce c i (Real.exp (-h) * x)) h := by
  have yPositive : 0 < Real.exp (-h) * x := mul_pos (Real.exp_pos _) positive
  have yBounded : Real.exp (-h) * x ≤ q := by
    calc
      _ ≤ Real.exp (-h) * (q * Real.exp h) := mul_le_mul_of_nonneg_left bounded (Real.exp_pos _).le
      _ = q := by rw [← mul_left_comm, ← Real.exp_add]; simp
  have exponent := (hasDerivAt_id h).neg.div_const (2 : ℝ)
  have amplitude : HasDerivAt (fun s : ℝ => Real.exp (-s/2)) (-(Real.exp (-h/2)/2)) h := by
    convert! (Real.hasDerivAt_exp (-h / 2)).comp h exponent using 1; ring
  have argument : HasDerivAt (fun s : ℝ => Real.exp (-s) * x) (-(Real.exp (-h) * x)) h := by
    convert! (((Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_id h).neg).mul_const x) using 1; ring
  have generated := amplitude.ofReal_comp.mul
    ((profile_derivative c i _ yPositive).scomp h (h:=fun s : ℝ => Real.exp (-s) * x) argument)
  simp only [Function.comp_apply, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, neg_mul] at generated
  convert! generated using 1
  have source := actual_profile_ODE c i _ yPositive yBounded
  simp only [Complex.ofReal_mul] at source
  unfold sourceHRate
  rw [← source]
  ring


private theorem source_derivative_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0 < x) : ContinuousAt (sourceDerivative c i) x := by
  fin_cases i
  · change ContinuousAt (sourceRawDerivative c) x
    unfold sourceRawDerivative
    exact (((continuousAt_const.mul (Translator.ForcingWhole.raw_continuousAt c positive.ne')).add
      (continuousAt_const.mul (Edge.raw_continuous q).continuousAt)).div
        Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr positive.ne')).add
      (Constructor.fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous c)).continuousAt
  · exact (burnolRieszReturnRawDerivative_continuous c).continuousAt

private def testDerivative (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![sourceRawDerivative c, positionExteriorDerivative c]

private theorem test_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0 < x) : HasDerivAt (exteriorTestRaw c i) (testDerivative c i x) x := by
  fin_cases i
  · change HasDerivAt (burnolRieszFourierExteriorRaw c) (sourceRawDerivative c x) x
    rw [funext (fourier_exterior_source_read c)]
    exact (sourceRaw_hasDerivAt c x positive.ne').add_const _
  · change HasDerivAt (burnolRieszStatePositiveOuterRaw c) (positionExteriorDerivative c x) x
    rw [funext (position_exterior_return_read c)]
    exact ((burnolMellinTailPower_hasDerivAt (star c.value) positive).const_mul (1 / 2 : ℂ)).sub
      ((burnolRieszReturnRaw_hasDerivAt c x).add_const _)

private theorem test_derivative_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (x : ℝ) (positive : 0 < x) : ContinuousAt (testDerivative c i) x := by
  fin_cases i
  · exact source_derivative_continuous c 0 x positive
  · change ContinuousAt (positionExteriorDerivative c) x
    unfold positionExteriorDerivative
    exact (continuousAt_const.mul (continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const x (-(star c.value + 1)) (Or.inr positive.ne')))).sub
      (burnolRieszReturnRawDerivative_continuous c).continuousAt

private theorem even_half_integral (f : ℝ → ℂ) (integrable : IntegrableOn f (symmetricInterval q))
    (even : ∀ x, f (-x) = f x) :
    (∫ x : ℝ in symmetricInterval q, f x) = 2 * ∫ x : ℝ in Ioc 0 q, f x := by
  have first : IntegrableOn f (Ioc (-q) 0) := integrable.mono_set (by intro x inside; exact ⟨inside.1.le,inside.2.trans (by norm_num)⟩)
  have second : IntegrableOn f (Ioc 0 q) := integrable.mono_set (by intro x inside; exact ⟨by linarith [inside.1],inside.2⟩)
  have split := setIntegral_union (Ioc_disjoint_Ioc_of_le (a := -q) (b := (0:ℝ)) (c := 0) (d := q) le_rfl)
    measurableSet_Ioc first second
  rw [Ioc_union_Ioc_eq_Ioc (by norm_num : -q ≤ (0:ℝ)) (by norm_num : (0:ℝ) ≤ q)] at split
  have reflected : (∫ x : ℝ in Ioc (-q) 0, f x) = ∫ x : ℝ in Ioc 0 q, f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : -q ≤ (0:ℝ)),
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ q)]
    have result := intervalIntegral.integral_comp_neg (f:=f) (a:=0) (b:=q)
    rw [show (fun x => f (-x)) = f from funext even,neg_zero] at result
    exact result.symm
  change (∫ x : ℝ in Icc (-q) q, f x) = _
  rw [integral_Icc_eq_integral_Ioc,split,reflected]
  ring

open private column_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source in
private theorem actual_window_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    ((burnolQuarterRestriction (burnolMultiplicativeDilation (-h)
      (burnolQuarterZeroExtension (sourceColumn c i : BurnolQuarterIntervalL2)))) : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)]
        (fun x => (Real.exp (-h/2) : ℂ) * sourceProfile c i (Real.exp (-h) * x)) := by
  let whole := burnolQuarterZeroExtension (sourceColumn c i : BurnolQuarterIntervalL2)
  let moved := burnolMultiplicativeDilation (-h) whole
  have rawMoved := (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (Real.exp_ne_zero (-h))).ae (column_raw c i)
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) moved,
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (-h) whole),ae_restrict_of_ae rawMoved,
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x restricted dilated raw inside
  have scaled : Real.exp (-h) * x ∈ symmetricInterval q := by
    change -q ≤ Real.exp (-h) * x ∧ Real.exp (-h) * x ≤ q
    have lower := mul_le_mul_of_nonneg_left inside.1 (Real.exp_pos (-h)).le
    have upper := mul_le_mul_of_nonneg_left inside.2 (Real.exp_pos (-h)).le
    have small := Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)
    constructor <;> nlinarith
  have restrictedAt : (burnolQuarterRestriction moved : ℝ → ℂ) x = moved x := restricted
  change (burnolQuarterRestriction moved : ℝ → ℂ) x = _
  rw [restrictedAt]
  rw [dilated]
  change (Real.exp (-h/2):ℂ) * whole (Real.exp (-h) * x) = _
  change whole (Real.exp (-h) * x) = (symmetricInterval q).indicator (sourceProfile c i) (Real.exp (-h) * x) at raw
  rw [raw,indicator_of_mem scaled]

private def sourcePrimitive (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (u : ℝ) : ℂ :=
  ∫ x : ℝ in (0:ℝ)..u, sourceProfile c i x

open private profile_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source in
private theorem actual_mean_primitive (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    centeringMean c h i = 4 * (Real.exp (h/2) : ℂ) * sourcePrimitive c i (q * Real.exp (-h)) := by
  let moved := burnolMultiplicativeDilation (-h) (burnolQuarterZeroExtension (sourceColumn c i : BurnolQuarterIntervalL2))
  let restricted := burnolQuarterRestriction moved
  have raw := actual_window_raw c h nonnegative i
  have integrable : IntegrableOn (fun x => (Real.exp (-h/2):ℂ) * sourceProfile c i (Real.exp (-h) * x)) (symmetricInterval q) :=
    ((Lp.memLp restricted).integrable (by norm_num)).congr raw
  have even : ∀ x : ℝ, (Real.exp (-h/2):ℂ) * sourceProfile c i (Real.exp (-h) * (-x)) =
      (Real.exp (-h/2):ℂ) * sourceProfile c i (Real.exp (-h) * x) := by
    intro x
    rw [mul_neg,profile_even]
  change burnolQuarterMeanCoefficient restricted = _
  rw [Constructor.mean_integral,integral_congr_ae raw,even_half_integral _ integrable even,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ q),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ (Real.exp_ne_zero (-h))]
  simp only [mul_zero,Complex.real_smul]
  have scale : Real.exp (-h/2) * (Real.exp (-h))⁻¹ = Real.exp (h/2) := by
    rw [← Real.exp_neg,neg_neg,← Real.exp_add]
    congr 1
    ring
  have coefficient : (Real.exp (-h/2):ℂ) * ((Real.exp (-h))⁻¹:ℝ) = (Real.exp (h/2):ℂ) := by
    rw [← Complex.ofReal_mul,scale]
  unfold sourcePrimitive
  rw [mul_comm (Real.exp (-h)) q]
  linear_combination (norm:=ring_nf) 4 * coefficient * (∫ x : ℝ in (0:ℝ)..(q * Real.exp (-h)), sourceProfile c i x)


private theorem profile_integrable (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    IntegrableOn (sourceProfile c i) (symmetricInterval q) := by
  fin_cases i
  · exact ((Lp.memLp (OriginalKCoefficientBFiniteAction.sourceB c : BurnolQuarterIntervalL2)).integrable (by norm_num)).congr
      (burnolRieszSingleFourierSource_ae_raw c)
  · exact (burnolRieszReturnRaw_continuous c).integrableOn_Icc

open private profile_measurable
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.RVolterra in
private theorem primitive_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (u : ℝ) (positive : 0 < u) (bounded : u ≤ q) :
    HasDerivAt (sourcePrimitive c i) (sourceProfile c i u) u := by
  have integrable : IntervalIntegrable (sourceProfile c i) volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le positive.le).mpr
      ((profile_integrable c i).mono_set (by intro x inside; exact ⟨by linarith [inside.1],inside.2.trans bounded⟩))
  exact intervalIntegral.integral_hasDerivAt_right integrable
    (profile_measurable c i).stronglyMeasurable.stronglyMeasurableAtFilter
    (profile_derivative c i u positive).continuousAt

private def meanExpression (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (h : ℝ) : ℂ :=
  4 * (Real.exp (h/2) : ℂ) * sourcePrimitive c i (q * Real.exp (-h))

private theorem meanExpression_derivative (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    HasDerivAt (meanExpression c i)
      (centeringMean c h i / 2 - (Real.exp (-h/2):ℂ) * sourceProfile c i (q * Real.exp (-h))) h := by
  have yPositive : 0 < q * Real.exp (-h) := mul_pos (by norm_num) (Real.exp_pos _)
  have yBounded : q * Real.exp (-h) ≤ q := by
    have scale := Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)
    nlinarith
  have amplitude : HasDerivAt (fun s : ℝ => Real.exp (s/2)) (Real.exp (h/2)/2) h := by
    convert! (Real.hasDerivAt_exp (h/2)).comp h ((hasDerivAt_id h).div_const 2) using 1; ring
  have argument : HasDerivAt (fun s : ℝ => q * Real.exp (-s)) (-(q * Real.exp (-h))) h := by
    convert! (((Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_id h).neg).const_mul q) using 1; ring
  have generated := ((amplitude.ofReal_comp.const_mul 4).mul
    ((primitive_derivative c i _ yPositive yBounded).scomp h (h:=fun s : ℝ => q * Real.exp (-s)) argument))
  convert! generated using 1
  rw [actual_mean_primitive c h nonnegative i]
  have scale : Real.exp (h/2) * Real.exp (-h) = Real.exp (-h/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have complexScale : (Real.exp (h/2):ℂ) * (Real.exp (-h):ℂ) = (Real.exp (-h/2):ℂ) := by rw [← Complex.ofReal_mul,scale]
  norm_num only [Function.comp_apply,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_one]
  linear_combination (norm:=ring_nf) complexScale * sourceProfile c i (q * Real.exp (-h))

theorem actual_mean_h_action (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    (h : ℝ) (positive : 0 < h) :
    HasDerivAt (fun s => centeringMean c s i)
      (centeringMean c h i / 2 - (Real.exp (-h/2):ℂ) * sourceProfile c i (q * Real.exp (-h))) h := by
  apply (meanExpression_derivative c i h positive.le).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds positive] with s inside
  exact actual_mean_primitive c s inside.le i

/-- Zero is the original override value; the subsequent derivative is one-sided. -/
theorem actual_full_loss_zero (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    FullUnit.fullSource c 0 i = 0 ∧ inner ℂ (physicalTest c i) (FullUnit.fullSource c 0 i) = 0 := by
  have original : FullUnit.fullSource c 0 i = 0 :=
    OriginalKSourceFiniteUpdate.OriginalBFiniteAction.fullWindowLoss_zero (sourceColumn c i)
  exact ⟨original,by rw [original,inner_zero_right]⟩


end OriginalKExteriorWindowHAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
