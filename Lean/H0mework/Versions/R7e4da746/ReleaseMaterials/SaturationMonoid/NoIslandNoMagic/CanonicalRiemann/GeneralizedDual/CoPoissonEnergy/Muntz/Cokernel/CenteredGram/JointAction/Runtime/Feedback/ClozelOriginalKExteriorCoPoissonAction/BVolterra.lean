import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.RVolterra

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorBRVolterra
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalKExteriorCoPoissonAction OriginalKExteriorRVolterra
open scoped InnerProductSpace Topology
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => (volume.restrict (symmetricInterval q))

def vRaw (x : ℝ) : ℂ := burnolMeanZeroFourierRaw Response.u x

def uRaw (x : ℝ) : ℂ := Edge.raw q x - Translator.ForcingMeanZero.edgeMean +
  burnolMeanZeroFourierRaw Response.v x

private theorem vRaw_read : ((Response.v : Hq) : ℝ → ℂ) =ᵐ[μq] vRaw :=
  burnolMeanZeroFourier_ae_raw Response.u

private theorem uRaw_read : ((Response.u : Hq) : ℝ → ℂ) =ᵐ[μq] uRaw := by
  have source : Response.u = Response.eta + burnolMeanZeroTruncatedFourier Response.v :=
    sub_eq_iff_eq_add.mp Response.source_pair_equation
  have native := congrArg (fun value : BurnolQuarterMeanZeroCarrier => (value : Hq)) source
  change (Response.u : Hq) = (Response.eta : Hq) +
    (burnolMeanZeroTruncatedFourier Response.v : Hq) at native
  rw [native]
  have eta := Translator.ForcingMeanZero.eta_read
  change ((Response.eta : Hq) : ℝ → ℂ) =ᵐ[μq]
    fun x => Edge.raw q x - Translator.ForcingMeanZero.edgeMean at eta
  filter_upwards [Lp.coeFn_add (Response.eta : Hq)
    (burnolMeanZeroTruncatedFourier Response.v : Hq), eta,
    burnolMeanZeroFourier_ae_raw Response.v] with x added first second
  simp only [Pi.add_apply] at added
  rw [added, first, second]
  rfl

private theorem vRaw_continuous : Continuous vRaw := by
  exact (burnolRadiusTruncatedFourierRaw_continuous (Response.u : Hq)).sub continuous_const

private theorem uRaw_continuous : Continuous uRaw := by
  exact ((Edge.raw_continuous q).sub continuous_const).add
    ((burnolRadiusTruncatedFourierRaw_continuous (Response.v : Hq)).sub continuous_const)

def bForce (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  Kernel.A c * uRaw x - Kernel.beta c * vRaw x + Kernel.beta c

private theorem weighted_source_read (c : BurnolCompletedMellinCoordinate) :
    weightedRaw c =ᵐ[μq] fun x =>
      (star c.value - 1 / 2) * burnolRieszSingleFourierSourceRaw c x + bForce c x := by
  let base : Hq := (star c.value - 1 / 2) • (burnolRieszSingleFourierSource c : Hq)
  let first : Hq := Kernel.A c • (Response.u : Hq)
  let second : Hq := Kernel.beta c • (Response.v : Hq)
  let unit : Hq := Kernel.beta c • intervalConstant q
  have native : weightedState c = base + first - second + unit := by
    unfold weightedState
    have generated := congrArg (fun value : BurnolQuarterMeanZeroCarrier => (value : Hq))
      (Euler.sourceEuler_eq c)
    change (Euler.sourceEuler c : Hq) = base + first - second at generated
    rw [generated]
  have reads : ((weightedState c : Hq) : ℝ → ℂ) =ᵐ[μq] fun x =>
      (star c.value - 1 / 2) * burnolRieszSingleFourierSourceRaw c x + bForce c x := by
    rw [native]
    filter_upwards [Lp.coeFn_add (base + first - second) unit,
      Lp.coeFn_sub (base + first) second, Lp.coeFn_add base first,
      Lp.coeFn_smul (star c.value - 1 / 2) (burnolRieszSingleFourierSource c : Hq),
      Lp.coeFn_smul (Kernel.A c) (Response.u : Hq),
      Lp.coeFn_smul (Kernel.beta c) (Response.v : Hq),
      Lp.coeFn_smul (Kernel.beta c) (intervalConstant q),
      burnolRieszSingleFourierSource_ae_raw c, uRaw_read, vRaw_read,
      intervalConstant_coeFn q] with x added subtracted pair baseAt firstAt secondAt unitAt
        sourceAt uAt vAt one
    change base x = _ at baseAt
    change first x = _ at firstAt
    change second x = _ at secondAt
    change unit x = _ at unitAt
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      at added subtracted pair baseAt firstAt secondAt unitAt
    rw [added, subtracted, pair, baseAt, firstAt, secondAt, unitAt, sourceAt, uAt, vAt, one]
    unfold bForce
    ring
  exact (weightedState_read c).symm.trans reads

theorem actual_b_source_ODE (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (positive : 0 < x) (bounded : x ≤ q) :
    (x : ℂ) * sourceRawDerivative c x + (1 - star c.value) * burnolRieszSingleFourierSourceRaw c x =
      bForce c x := by
  have restricted : weightedRaw c =ᵐ[volume.restrict (Icc (x / 2) q)] fun y =>
      (star c.value - 1 / 2) * burnolRieszSingleFourierSourceRaw c y + bForce c y :=
    ae_restrict_of_ae_restrict_of_subset
      (show Icc (x / 2) q ⊆ symmetricInterval q by intro y inside; constructor <;> linarith [inside.1, inside.2])
      (weighted_source_read c)
  have leftRegular : ContinuousOn (weightedRaw c) (Icc (x / 2) q) := by
    rw [funext (weightedRaw_eq c)]
    intro y inside
    have nonzero : y ≠ 0 := ne_of_gt (by linarith [inside.1] : 0 < y)
    exact ((((Translator.ForcingWhole.raw_continuousAt c nonzero).const_mul
      (star c.value - 1 / 2)).add
      ((Edge.raw_continuous q).continuousAt.const_mul
        (star c.value * GapEuler.gapMean q c))).add
      (Constructor.secondEulerRaw_continuous c).continuousAt).sub
      continuousAt_const |>.continuousWithinAt
  have rightRegular : ContinuousOn (fun y =>
      (star c.value - 1 / 2) * burnolRieszSingleFourierSourceRaw c y + bForce c y) (Icc (x / 2) q) := by
    intro y inside
    have nonzero : y ≠ 0 := ne_of_gt (by linarith [inside.1] : 0 < y)
    exact ((burnolRieszSingleFourierSourceRaw_continuousAt c nonzero).const_mul
      (star c.value - 1 / 2)).add
      ((((uRaw_continuous.continuousAt.const_mul (Kernel.A c)).sub
        (vRaw_continuous.continuousAt.const_mul (Kernel.beta c))).add
        continuousAt_const)) |>.continuousWithinAt
  have point := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ)
    (show x / 2 ≠ q by linarith) restricted leftRegular rightRegular
      (show x ∈ Icc (x / 2) q by constructor <;> linarith)
  have generated := sourceRaw_weighted_eq c x positive.ne'
  rw [point] at generated
  linear_combination generated


def bDrift (c : BurnolCompletedMellinCoordinate) : ℂ := (c.value + star c.value - 1) / 2

def bKernel (c : BurnolCompletedMellinCoordinate) (h x tau : ℝ) : ℂ :=
  Complex.exp ((-c.value / 2) * (tau : ℂ)) *
    burnolRieszSingleFourierSourceRaw c (Real.exp (-h - tau / 2) * |x|)

def bForcingKernel (c : BurnolCompletedMellinCoordinate) (h x tau : ℝ) : ℂ :=
  Complex.exp ((-c.value / 2) * (tau : ℂ)) * bForce c (Real.exp (-h - tau / 2) * |x|)

theorem actual_b_kernel_derivative (c : BurnolCompletedMellinCoordinate) (h x tau : ℝ)
    (positive : 0 < Real.exp (-h - tau / 2) * |x|)
    (bounded : Real.exp (-h - tau / 2) * |x| ≤ q) :
    HasDerivAt (bKernel c h x)
      (-bDrift c * bKernel c h x tau - (1 / 2 : ℂ) * bForcingKernel c h x tau) tau := by
  have cast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 tau := Complex.ofRealCLM.hasDerivAt
  have character := (cast.const_mul (-c.value / 2)).cexp
  have argument : HasDerivAt (fun t : ℝ => Real.exp (-h - t / 2) * |x|)
      (-(Real.exp (-h - tau / 2) * |x|) / 2) tau := by
    convert! (((hasDerivAt_const tau (-h)).sub ((hasDerivAt_id tau).div_const 2)).exp).mul_const |x| using 1
    simp only [id_eq, Pi.sub_apply]
    ring
  have generated := character.mul ((sourceRaw_hasDerivAt c _ positive.ne').scomp tau argument)
  simp only [Function.comp_apply, mul_one] at generated
  convert! generated using 1
  have source := actual_b_source_ODE c _ positive bounded
  unfold bDrift bKernel bForcingKernel
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.real_smul]
  rw [← source]
  ring

def linearWindowWeight (d : ℂ) (b s : ℝ) : ℂ :=
  Complex.exp (d * (s : ℂ)) * ∫ t : ℝ in s..b, Complex.exp (-d * (t : ℂ))

private theorem linearWindowWeight_derivative (d : ℂ) (b s : ℝ) :
    HasDerivAt (linearWindowWeight d b) (d * linearWindowWeight d b s - 1) s := by
  have cast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
  have character := (cast.const_mul d).cexp
  have regular : Continuous (fun t : ℝ => Complex.exp (-d * (t : ℂ))) := by fun_prop
  have primitive := intervalIntegral.integral_hasDerivAt_left
    (regular.intervalIntegrable s b) regular.stronglyMeasurable.stronglyMeasurableAtFilter regular.continuousAt
  convert! character.mul primitive using 1
  unfold linearWindowWeight
  have inverse : Complex.exp (d * (s : ℂ)) * Complex.exp (-d * (s : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  linear_combination inverse

private theorem linearWindowWeight_continuous (d : ℂ) (b : ℝ) : Continuous (linearWindowWeight d b) :=
  continuous_iff_continuousAt.mpr fun s => (linearWindowWeight_derivative d b s).continuousAt

private theorem linear_source_integral (d : ℂ) (a b : ℝ) (ordered : a ≤ b) (G F : ℝ → ℂ)
    (regularG : ContinuousOn G (Icc a b)) (regularF : ContinuousOn F (Icc a b))
    (generated : ∀ s ∈ Icc a b, HasDerivAt G (-d * G s - (1 / 2 : ℂ) * F s) s) :
    (∫ s : ℝ in a..b, G s) = linearWindowWeight d b a * G a - (1 / 2 : ℂ) *
      ∫ s : ℝ in a..b, linearWindowWeight d b s * F s := by
  have productDerivative (s : ℝ) (inside : s ∈ uIcc a b) :
      HasDerivAt (fun s => linearWindowWeight d b s * G s)
        (-G s - (1 / 2 : ℂ) * (linearWindowWeight d b s * F s)) s := by
    rw [uIcc_of_le ordered] at inside
    convert! (linearWindowWeight_derivative d b s).mul (generated s inside) using 1
    ring
  have first : IntervalIntegrable (fun s => -G s) volume a b :=
    regularG.neg.intervalIntegrable_of_Icc ordered
  have second : IntervalIntegrable (fun s => (1 / 2 : ℂ) * (linearWindowWeight d b s * F s)) volume a b :=
    (((linearWindowWeight_continuous d b).continuousOn.mul regularF).const_mul (1 / 2 : ℂ)).intervalIntegrable_of_Icc ordered
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt productDerivative (first.sub second)
  have atEnd : linearWindowWeight d b b = 0 := by simp [linearWindowWeight]
  rw [intervalIntegral.integral_sub first second, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, atEnd, zero_mul] at actual
  linear_combination -actual

def bRRaw (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  if q < |x| then
    let b := timeUpper x;
    let a := max 0 (b - 2 * h);
    -(Real.exp (-h / 2) : ℂ) *
      (linearWindowWeight (bDrift c) b a * bKernel c h x a - (1 / 2 : ℂ) *
        ∫ s : ℝ in a..b, linearWindowWeight (bDrift c) b s * bForcingKernel c h x s)
  else 0

theorem actual_b_R_source (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    (burnolDirectRightResolvent (c.value / 2) (exteriorSource c h 0) : ℝ → ℂ) =ᵐ[volume]
      bRRaw c h := by
  filter_upwards [actual_finite_R_source c h nonnegative 0] with x actual
  rw [actual]
  by_cases outside : q < |x|
  · let b := timeUpper x
    let a := max 0 (b - 2 * h)
    have xPositive : 0 < |x| := lt_trans (by norm_num) outside
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
        exact ⟨⟨(le_max_right 0 _).trans lower.le, strict⟩, (le_max_left 0 _).trans_lt lower⟩
    have generated (s : ℝ) (inside : s ∈ Icc a b) :
        HasDerivAt (bKernel c h x)
          (-bDrift c * bKernel c h x s - (1 / 2 : ℂ) * bForcingKernel c h x s) s := by
      apply actual_b_kernel_derivative
      · exact mul_pos (Real.exp_pos _) xPositive
      · have reconstruct : |x| = q * Real.exp (b / 2) := by
          dsimp only [b, timeUpper]
          rw [show 2 * Real.log (4 * |x|) / 2 = Real.log (4 * |x|) by ring,
            Real.exp_log (mul_pos (by norm_num) xPositive)]
          ring
        have profile : Real.exp (-h - s / 2) * |x| = q * Real.exp ((b - 2 * h - s) / 2) := by
          rw [reconstruct, ← mul_assoc, mul_comm (Real.exp _) q, mul_assoc, ← Real.exp_add]
          congr 2
          ring
        have lower : b - 2 * h ≤ s := (le_max_right 0 _).trans inside.1
        rw [profile]
        exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (by norm_num : 0 ≤ q)).trans_eq (mul_one q)
    have regularG : ContinuousOn (bKernel c h x) (Icc a b) :=
      fun s inside => (generated s inside).continuousAt.continuousWithinAt
    have regularForce : Continuous (bForce c) := by
      unfold bForce
      exact ((uRaw_continuous.const_mul _).sub (vRaw_continuous.const_mul _)).add continuous_const
    have regularF : Continuous (bForcingKernel c h x) := by
      unfold bForcingKernel
      fun_prop
    rw [bRRaw, if_pos outside]
    change -(Real.exp (-h / 2) : ℂ) * (∫ s : ℝ in timeWindow h x, bKernel c h x s) = _
    rw [setIntegral_congr_set sameSets, ← intervalIntegral.integral_of_le ordered,
      linear_source_integral (bDrift c) a b ordered (bKernel c h x) (bForcingKernel c h x)
        regularG regularF.continuousOn generated]
  · have bNonpositive : timeUpper x ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      exact Real.log_nonpos (mul_nonneg (by norm_num) (abs_nonneg x)) (by linarith)
    have empty : timeWindow h x = ∅ := by
      ext s
      simp only [timeWindow, mem_inter_iff, mem_Ico, mem_Ioi, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, upper⟩, positive⟩
      linarith
    rw [bRRaw, if_neg outside]
    simp only [finiteRRaw, empty, setIntegral_empty, mul_zero]

end
end OriginalKExteriorBRVolterra
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
