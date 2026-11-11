import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.FullUnit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.RawReturn
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitRegularity.GeneratorCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorRVolterra

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKExteriorCoPoissonAction OriginalPaPhysicalGreen OriginalRieszSource
open OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open scoped InnerProductSpace Topology
noncomputable section

local notation "q" => (1 / 4 : ℝ)

def shellRaw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) (x : ℝ) : ℂ :=
  if q < |x| ∧ |x| ≤ q * Real.exp h then
    (Real.exp (-h / 2) : ℂ) * sourceProfile c i (Real.exp (-h) * |x|)
  else 0

private theorem profile_measurable (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    Measurable (sourceProfile c i) := by
  fin_cases i
  · apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (burnolRieszSingleFourierSourceRaw_continuousAt c
      (by simpa only [mem_compl_iff, mem_singleton_iff] using outside)).continuousWithinAt
  · exact (burnolRieszReturnRaw_continuous c).measurable

theorem shellRaw_measurable (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    Measurable (shellRaw c h i) := by
  unfold shellRaw
  exact Measurable.ite
    ((measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const))
    (measurable_const.mul ((profile_measurable c i).comp (by fun_prop))) measurable_const

open private column_raw profile_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source in
theorem actual_source_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    (exteriorSource c h i : ℝ → ℂ) =ᵐ[volume] shellRaw c h i := by
  rw [actual_exterior_source c h nonnegative i]
  let whole := burnolQuarterZeroExtension (sourceColumn c i : BurnolQuarterIntervalL2)
  let moved := burnolMultiplicativeDilation (-h) whole
  have rawMoved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (Real.exp_ne_zero (-h))).ae (column_raw c i)
  filter_upwards [Lp.coeFn_sub moved (originalPhysicalCutoff q moved),
    originalPhysicalCutoff_coeFn q moved, burnolMultiplicativeDilation_coeFn (-h) whole,
    rawMoved] with x subAt cutAt dilationAt rawAt
  change (moved - originalPhysicalCutoff q moved : BurnolL2) x = _
  rw [subAt]
  change moved x - originalPhysicalCutoff q moved x = _
  rw [cutAt]
  have movedInside : Real.exp (-h) * x ∈ symmetricInterval q ↔ |x| ≤ q * Real.exp h := by
    change (-q ≤ Real.exp (-h) * x ∧ Real.exp (-h) * x ≤ q) ↔ _
    rw [← abs_le, abs_mul, abs_of_pos (Real.exp_pos (-h))]
    have identity : Real.exp (-h) * (q * Real.exp h) = q := by
      rw [Real.exp_neg]
      field_simp
    constructor
    · intro upper
      exact (mul_le_mul_iff_right₀ (Real.exp_pos (-h))).mp (upper.trans_eq identity.symm)
    · intro upper
      exact (mul_le_mul_of_nonneg_left upper (Real.exp_pos (-h)).le).trans_eq identity
  have evenRead : sourceProfile c i (Real.exp (-h) * x) =
      sourceProfile c i (Real.exp (-h) * |x|) := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, mul_neg, profile_even]
  change whole (Real.exp (-h) * x) =
    (symmetricInterval q).indicator (sourceProfile c i) (Real.exp (-h) * x) at rawAt
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, sub_self, shellRaw, if_neg]
    exact fun active => not_lt_of_ge (abs_le.mpr inside) active.1
  · rw [indicator_of_notMem inside, sub_zero]
    change burnolMultiplicativeDilation (-h) whole x = _
    rw [dilationAt]
    change (Real.exp (-h / 2) : ℂ) * whole (Real.exp (-h) * x) = _
    rw [rawAt]
    by_cases upper : |x| ≤ q * Real.exp h
    · rw [indicator_of_mem (movedInside.mpr upper), evenRead, shellRaw, if_pos]
      exact ⟨lt_of_not_ge (fun small => inside (abs_le.mp small)), upper⟩
    · rw [indicator_of_notMem (fun member => upper (movedInside.mp member)), mul_zero,
        shellRaw, if_neg (fun active => upper active.2)]

def rKernel (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) (p : ℝ × ℝ) : ℂ :=
  Complex.exp ((-c.value / 2) * (p.1 : ℂ)) *
    shellRaw c h i (Real.exp (-p.1 / 2) * p.2)

theorem actual_source_R_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    (burnolDirectRightResolvent (c.value / 2) (exteriorSource c h i) : ℝ → ℂ) =ᵐ[volume]
      fun x => -(∫ tau : ℝ in Ioi 0, rKernel c h i (tau, x)) := by
  let z := c.value / 2
  have right : 1 / 4 < z.re := by
    dsimp only [z]
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  let family := burnolDirectRightResolventIntegrand z (exteriorSource c h i)
  have measured : Measurable (rKernel c h i) := by
    unfold rKernel
    have character : Measurable (fun p : ℝ × ℝ =>
        Complex.exp ((-c.value / 2) * (p.1 : ℂ))) := by fun_prop
    exact character.mul ((shellRaw_measurable c h i).comp (by fun_prop))
  have reads : ∀ᵐ tau ∂volume.restrict (Ioi 0),
      (family tau : ℝ → ℂ) =ᵐ[volume] fun x => rKernel c h i (tau, x) := by
    filter_upwards with tau
    have sourceRead := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (Real.exp_ne_zero (-tau / 2))).ae (actual_source_raw c h nonnegative i)
    filter_upwards [Lp.coeFn_smul (positiveMellinQuarterRightResolventWeight z tau)
      (burnolMultiplicativeDilation (-tau / 2) (exteriorSource c h i)),
      burnolMultiplicativeDilation_coeFn (-tau / 2) (exteriorSource c h i), sourceRead]
      with x scalar moved source
    unfold family burnolDirectRightResolventIntegrand
    rw [scalar]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [moved]
    unfold burnolL2RawNormalizedDilation
    simp only [smul_eq_mul] at source
    rw [source]
    unfold rKernel positiveMellinQuarterRightResolventWeight
    dsimp only
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp only [z]
    push_cast
    ring
  unfold burnolDirectRightResolvent
  filter_upwards [Lp.coeFn_neg (∫ tau : ℝ in Ioi 0, family tau),
    OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict (Ioi 0)) family
      (burnolDirectRightResolventIntegrand_integrableOn z right (exteriorSource c h i))
      (rKernel c h i) measured reads] with x negRead rawRead
  rw [negRead, Pi.neg_apply, rawRead]


def timeUpper (x : ℝ) : ℝ := 2 * Real.log (4 * |x|)

def timeWindow (h x : ℝ) : Set ℝ :=
  Ico (timeUpper x - 2 * h) (timeUpper x) ∩ Ioi 0

def finiteRRaw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) (x : ℝ) : ℂ :=
  -(Real.exp (-h / 2) : ℂ) * ∫ tau : ℝ in timeWindow h x,
    Complex.exp ((-c.value / 2) * (tau : ℂ)) *
      sourceProfile c i (Real.exp (-h - tau / 2) * |x|)

private theorem shell_entrance (h tau x : ℝ) (nonzero : x ≠ 0) :
    (q < Real.exp (-tau / 2) * |x| ∧
      Real.exp (-tau / 2) * |x| ≤ q * Real.exp h) ↔
        tau ∈ Ico (timeUpper x - 2 * h) (timeUpper x) := by
  have positive : 0 < 4 * |x| := mul_pos (by norm_num) (abs_pos.mpr nonzero)
  have reconstruct : |x| = q * Real.exp (timeUpper x / 2) := by
    unfold timeUpper
    rw [show 2 * Real.log (4 * |x|) / 2 = Real.log (4 * |x|) by ring,
      Real.exp_log positive]
    ring
  have scaled : Real.exp (-tau / 2) * |x| =
      q * Real.exp ((timeUpper x - tau) / 2) := by
    conv_lhs => rw [reconstruct]
    rw [← mul_assoc, mul_comm (Real.exp _) q, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [scaled]
  have first : q < q * Real.exp ((timeUpper x - tau) / 2) ↔ tau < timeUpper x := by
    have multiply : q < q * Real.exp ((timeUpper x - tau) / 2) ↔
        1 < Real.exp ((timeUpper x - tau) / 2) := by constructor <;> intro bound <;> linarith
    rw [multiply, Real.one_lt_exp_iff]
    constructor <;> intro bound <;> linarith
  have second : q * Real.exp ((timeUpper x - tau) / 2) ≤ q * Real.exp h ↔
      timeUpper x - 2 * h ≤ tau := by
    have multiply : q * Real.exp ((timeUpper x - tau) / 2) ≤ q * Real.exp h ↔
        Real.exp ((timeUpper x - tau) / 2) ≤ Real.exp h := by
      constructor <;> intro bound <;> linarith
    rw [multiply, Real.exp_le_exp]
    constructor <;> intro bound <;> linarith
  rw [first, second]
  exact and_comm

private theorem rKernel_window (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2)
    (tau x : ℝ) (nonzero : x ≠ 0) :
    rKernel c h i (tau, x) =
      (Real.exp (-h / 2) : ℂ) *
        (Ico (timeUpper x - 2 * h) (timeUpper x)).indicator
          (fun tau => Complex.exp ((-c.value / 2) * (tau : ℂ)) *
            sourceProfile c i (Real.exp (-h - tau / 2) * |x|)) tau := by
  unfold rKernel shellRaw
  dsimp only
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have entrance := shell_entrance h tau x nonzero
  by_cases active : tau ∈ Ico (timeUpper x - 2 * h) (timeUpper x)
  · rw [if_pos (entrance.mpr active), indicator_of_mem active]
    have argument : Real.exp (-h) * (Real.exp (-tau / 2) * |x|) =
        Real.exp (-h - tau / 2) * |x| := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring
    rw [argument]
    ring
  · rw [if_neg (fun source => active (entrance.mp source)), indicator_of_notMem active, mul_zero, mul_zero]

theorem actual_finite_R_source (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) :
    (burnolDirectRightResolvent (c.value / 2) (exteriorSource c h i) : ℝ → ℂ) =ᵐ[volume]
      finiteRRaw c h i := by
  filter_upwards [actual_source_R_raw c h nonnegative i, volume.ae_ne (0 : ℝ)] with x actual nonzero
  rw [actual]
  have kernel : (fun tau => rKernel c h i (tau, x)) =
      fun tau => (Real.exp (-h / 2) : ℂ) *
        (Ico (timeUpper x - 2 * h) (timeUpper x)).indicator
          (fun tau => Complex.exp ((-c.value / 2) * (tau : ℂ)) *
            sourceProfile c i (Real.exp (-h - tau / 2) * |x|)) tau :=
    funext (fun tau => rKernel_window c h i tau x nonzero)
  rw [kernel, integral_const_mul, integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico]
  simp only [finiteRRaw, timeWindow, neg_mul]

open private resolvent_realizes
  from H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitRegularity.GeneratorCounting in
 theorem actual_wave_R_realizes (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
      (burnolDirectRightResolvent (c.value / 2) (exteriorSource c h i)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolDirectRightResolvent (c.value / 2) (exteriorWave c h i))) test := by
  apply resolvent_realizes
  · rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  · intro test
    rw [actual_exterior_source c h nonnegative i]
    exact exterior_wave_realizes c h nonnegative i test


private def fourierRead (x : ℝ) : BurnolQuarterIntervalL2 →ₗ[ℂ] ℂ where
  toFun := fun state => burnolRadiusTruncatedFourierRaw q state x
  map_add' left right := congrFun (burnolRadiusTruncatedFourierRaw_add left right) x
  map_smul' scalar state := congrFun (burnolRadiusTruncatedFourierRaw_smul scalar state) x

def returnMean (c : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient
    (burnolTruncatedFourier (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2))

def returnForce (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  OriginalRieszSource.Kernel.beta c * OriginalRieszSource.Edge.raw q x -
    OriginalRieszSource.Kernel.A c * burnolRadiusTruncatedFourierRaw q
      (OriginalRieszSource.Response.u : BurnolQuarterIntervalL2) x +
    OriginalRieszSource.Kernel.beta c * burnolRadiusTruncatedFourierRaw q
      (OriginalRieszSource.Response.v : BurnolQuarterIntervalL2) x -
    star c.value * returnMean c

theorem actual_return_source_ODE (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    (x : ℂ) * burnolRieszReturnRawDerivative c x + star c.value * burnolRieszReturnRaw c x =
      returnForce c x := by
  have eulerRead := congrArg (fun value : BurnolQuarterMeanZeroCarrier =>
    fourierRead x (value : BurnolQuarterIntervalL2)) (Euler.sourceEuler_eq c)
  change fourierRead x (Euler.sourceEuler c : BurnolQuarterIntervalL2) =
    fourierRead x ((star c.value - 1 / 2) •
      (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2) +
      Kernel.A c • (Response.u : BurnolQuarterIntervalL2) -
      Kernel.beta c • (Response.v : BurnolQuarterIntervalL2)) at eulerRead
  simp only [map_sub, map_add, map_smul, smul_eq_mul] at eulerRead
  have source := Euler.source_kernel_ward c (Euler.sourceEuler c) (Euler.source_euler c) x
  change (x : ℂ) * burnolRieszReturnRawDerivative c x +
    (1 / 2 : ℂ) * fourierRead x (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2) +
    fourierRead x (Euler.sourceEuler c : BurnolQuarterIntervalL2) = Kernel.beta c * Edge.raw q x at source
  have raw : fourierRead x (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2) =
      burnolRieszReturnRaw c x + returnMean c := by
    unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw returnMean
    change _ = fourierRead x (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2) - _ + _
    ring
  rw [eulerRead, raw] at source
  unfold returnForce
  change _ = Kernel.beta c * Edge.raw q x - Kernel.A c *
    fourierRead x (Response.u : BurnolQuarterIntervalL2) + Kernel.beta c *
    fourierRead x (Response.v : BurnolQuarterIntervalL2) - star c.value * returnMean c
  linear_combination source

private theorem returnForce_continuous (c : BurnolCompletedMellinCoordinate) :
    Continuous (returnForce c) := by
  have edge := OriginalRieszSource.Edge.raw_continuous q
  have first := burnolRadiusTruncatedFourierRaw_continuous
    (OriginalRieszSource.Response.u : BurnolQuarterIntervalL2)
  have second := burnolRadiusTruncatedFourierRaw_continuous
    (OriginalRieszSource.Response.v : BurnolQuarterIntervalL2)
  unfold returnForce
  fun_prop

def crossDrift (c : BurnolCompletedMellinCoordinate) : ℂ := (c.value - star c.value) / 2

def returnKernel (c : BurnolCompletedMellinCoordinate) (h x tau : ℝ) : ℂ :=
  Complex.exp ((-c.value / 2) * (tau : ℂ)) *
    burnolRieszReturnRaw c (Real.exp (-h - tau / 2) * |x|)

def returnForcingKernel (c : BurnolCompletedMellinCoordinate) (h x tau : ℝ) : ℂ :=
  Complex.exp ((-c.value / 2) * (tau : ℂ)) *
    returnForce c (Real.exp (-h - tau / 2) * |x|)

theorem actual_return_kernel_derivative (c : BurnolCompletedMellinCoordinate) (h x tau : ℝ) :
    HasDerivAt (returnKernel c h x)
      (-crossDrift c * returnKernel c h x tau - (1 / 2 : ℂ) * returnForcingKernel c h x tau) tau := by
  have cast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 tau := Complex.ofRealCLM.hasDerivAt
  have character := (cast.const_mul (-c.value / 2)).cexp
  have argument : HasDerivAt (fun t : ℝ => Real.exp (-h - t / 2) * |x|)
      (-(Real.exp (-h - tau / 2) * |x|) / 2) tau := by
    convert! (((hasDerivAt_const tau (-h)).sub ((hasDerivAt_id tau).div_const 2)).exp).mul_const |x| using 1
    simp only [id_eq, Pi.sub_apply]
    ring
  have generated := character.mul ((burnolRieszReturnRaw_hasDerivAt c _).scomp tau argument)
  simp only [Function.comp_apply, mul_one] at generated
  convert! generated using 1
  have source := actual_return_source_ODE c (Real.exp (-h - tau / 2) * |x|)
  unfold crossDrift returnKernel returnForcingKernel
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.real_smul]
  rw [← source]
  ring

private theorem returnKernel_continuous (c : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    Continuous (returnKernel c h x) :=
  continuous_iff_continuousAt.mpr fun tau =>
    (actual_return_kernel_derivative c h x tau).continuousAt

private theorem returnForcingKernel_continuous (c : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    Continuous (returnForcingKernel c h x) := by
  have force := returnForce_continuous c
  unfold returnForcingKernel
  fun_prop

def windowWeight (c : BurnolCompletedMellinCoordinate) (b s : ℝ) : ℂ :=
  Complex.exp (crossDrift c * (s : ℂ)) *
    ∫ t : ℝ in s..b, Complex.exp (-crossDrift c * (t : ℂ))

private theorem windowWeight_derivative (c : BurnolCompletedMellinCoordinate) (b s : ℝ) :
    HasDerivAt (windowWeight c b)
      (crossDrift c * windowWeight c b s - 1) s := by
  have cast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
  have character := (cast.const_mul (crossDrift c)).cexp
  have regular : Continuous (fun t : ℝ => Complex.exp (-crossDrift c * (t : ℂ))) := by fun_prop
  have primitive := intervalIntegral.integral_hasDerivAt_left
    (regular.intervalIntegrable s b) regular.stronglyMeasurable.stronglyMeasurableAtFilter
    regular.continuousAt
  convert! character.mul primitive using 1
  unfold windowWeight
  have inverse : Complex.exp (crossDrift c * (s : ℂ)) *
      Complex.exp (-crossDrift c * (s : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  linear_combination inverse

private theorem windowWeight_continuous (c : BurnolCompletedMellinCoordinate) (b : ℝ) :
    Continuous (windowWeight c b) :=
  continuous_iff_continuousAt.mpr fun s => (windowWeight_derivative c b s).continuousAt

theorem actual_return_finite_forcing (c : BurnolCompletedMellinCoordinate) (h x a b : ℝ) :
    (∫ s : ℝ in a..b, returnKernel c h x s) =
      windowWeight c b a * returnKernel c h x a - (1 / 2 : ℂ) *
        ∫ s : ℝ in a..b, windowWeight c b s * returnForcingKernel c h x s := by
  have productDerivative (s : ℝ) :
      HasDerivAt (fun s => windowWeight c b s * returnKernel c h x s)
        (-returnKernel c h x s - (1 / 2 : ℂ) *
          (windowWeight c b s * returnForcingKernel c h x s)) s := by
    convert! (windowWeight_derivative c b s).mul (actual_return_kernel_derivative c h x s) using 1
    ring
  have firstIntegrable : IntervalIntegrable (fun s => -returnKernel c h x s) volume a b :=
    (returnKernel_continuous c h x).neg.intervalIntegrable a b
  have secondIntegrable : IntervalIntegrable (fun s => (1 / 2 : ℂ) *
      (windowWeight c b s * returnForcingKernel c h x s)) volume a b :=
    (((windowWeight_continuous c b).mul (returnForcingKernel_continuous c h x)).const_mul
      (1 / 2 : ℂ)).intervalIntegrable a b
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => productDerivative s) (firstIntegrable.sub secondIntegrable)
  have weightEnd : windowWeight c b b = 0 := by simp [windowWeight]
  rw [intervalIntegral.integral_sub firstIntegrable secondIntegrable,
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, weightEnd, zero_mul] at actual
  linear_combination -actual


def returnRRaw (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  if q < |x| then
    let b := timeUpper x;
    let a := max 0 (b - 2 * h);
    -(Real.exp (-h / 2) : ℂ) *
      (windowWeight c b a * returnKernel c h x a - (1 / 2 : ℂ) *
        ∫ s : ℝ in a..b, windowWeight c b s * returnForcingKernel c h x s)
  else 0

theorem actual_return_R_source (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    (burnolDirectRightResolvent (c.value / 2) (exteriorSource c h 1) : ℝ → ℂ) =ᵐ[volume]
      returnRRaw c h := by
  filter_upwards [actual_finite_R_source c h nonnegative 1] with x actual
  rw [actual]
  by_cases outside : q < |x|
  · let b := timeUpper x
    let a := max 0 (b - 2 * h)
    have bPositive : 0 < b := mul_pos (by norm_num) (Real.log_pos (by linarith : 1 < 4 * |x|))
    have ordered : a ≤ b := max_le bPositive.le (by linarith)
    have sameSets : timeWindow h x =ᵐ[volume] Ioc a b := by
      filter_upwards [volume.ae_ne a, volume.ae_ne b] with s notLower notUpper
      apply propext
      change ((b - 2 * h ≤ s ∧ s < b) ∧ 0 < s) ↔ a < s ∧ s ≤ b
      constructor
      · rintro ⟨⟨lower, upper⟩, positive⟩
        have bound : a ≤ s := max_le positive.le lower
        have strict : a < s := by
          rcases lt_or_eq_of_le bound with strict | equal
          · exact strict
          · exact (notLower equal.symm).elim
        exact ⟨strict, upper.le⟩
      · rintro ⟨lower, upper⟩
        have strict : s < b := by
          rcases lt_or_eq_of_le upper with strict | equal
          · exact strict
          · exact (notUpper equal).elim
        exact ⟨⟨(le_max_right 0 _).trans lower.le, strict⟩,
          (le_max_left 0 _).trans_lt lower⟩
    rw [returnRRaw, if_pos outside]
    change -(Real.exp (-h / 2) : ℂ) *
      (∫ s : ℝ in timeWindow h x, returnKernel c h x s) = _
    rw [setIntegral_congr_set sameSets, ← intervalIntegral.integral_of_le ordered,
      actual_return_finite_forcing]
  · have bNonpositive : timeUpper x ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      exact Real.log_nonpos (mul_nonneg (by norm_num) (abs_nonneg x)) (by linarith)
    have empty : timeWindow h x = ∅ := by
      ext s
      simp only [timeWindow, mem_inter_iff, mem_Ico, mem_Ioi, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, upper⟩, positive⟩
      linarith
    rw [returnRRaw, if_neg outside]
    simp only [finiteRRaw, empty, setIntegral_empty, mul_zero]

end
end OriginalKExteriorRVolterra
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
