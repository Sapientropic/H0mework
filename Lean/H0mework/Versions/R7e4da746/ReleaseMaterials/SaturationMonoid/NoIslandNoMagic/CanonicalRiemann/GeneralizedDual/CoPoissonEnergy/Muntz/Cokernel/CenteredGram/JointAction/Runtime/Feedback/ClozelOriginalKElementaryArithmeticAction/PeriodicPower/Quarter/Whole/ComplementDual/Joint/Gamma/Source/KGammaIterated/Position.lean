import Mathlib.Analysis.Calculus.BumpFunction.Basic
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaGapLocalSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaSeedMellinDomain
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ExteriorFourierSource

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.KGamma.Iterated

open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace Real
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.JointLogConductor
open OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.ConductorDual OriginalGamma.Source.GammaGapLocal
open OriginalGamma.Source.GammaSeedExterior OriginalGamma.Source.GammaSeedMellinDomain

noncomputable section
local notation "F" => fourierL2
local notation "q" => (1/4 : ℝ)
local notation "edge" => (1/8 : ℝ)

open private fourier_l2_raw from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ExteriorFourierSource

private theorem log_schwartz_integrable (test : SchwartzMap ℝ ℂ) :
    Integrable (logSchwartzL2 test : ℝ → ℂ) := by
  let moment : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) test
  have momentRaw (x : ℝ) : moment x = (x : ℂ) * test x :=
    SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) test x
  have weighted : MemLp (fun x : ℝ => (1 + |x|) * ‖logSchwartzL2 test x‖) 2 volume := by
    apply ((Lp.memLp (logSchwartzL2 test)).norm.add (Lp.memLp (logSchwartzL2 moment)).norm).ae_eq
    filter_upwards [original_log_schwartz_raw test, original_log_schwartz_raw moment]
      with x raw weightedRaw
    simp only [Pi.add_apply, raw, weightedRaw, momentRaw, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    ring
  have domain := (gapLocalPaid% tail_weight_memLp).integrable_mul weighted
  apply domain.mono' (Lp.stronglyMeasurable (logSchwartzL2 test)).aestronglyMeasurable
  filter_upwards with x
  change ‖logSchwartzL2 test x‖ ≤ (1 + |x|)⁻¹ * ((1 + |x|) * ‖logSchwartzL2 test x‖)
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (1 + |x| : ℝ) ≠ 0), one_mul]

private def plateauBump : ContDiffBump (0 : ℝ) where
  rIn := q
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def plateau : SchwartzMap ℝ ℂ :=
  (plateauBump.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp plateauBump.contDiff)

private theorem plateau_one (x : ℝ) (inside : |x| < q) : plateau x = 1 := by
  change (plateauBump x : ℂ) = 1
  rw [plateauBump.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact inside.le), Complex.ofReal_one]

/-- A constant actual q-gap determines the logarithmic origin term of its generated Gamma field. -/
theorem actual_constant_gap_gamma_origin (v gamma : BurnolL2) (k : ℂ)
    (source : GammaPair v gamma) (constant : ∀ᵐ x : ℝ ∂volume, |x| < q → v x = k) :
    ∃ budget : ℝ, 0 ≤ budget ∧
      ∀ᵐ x : ℝ ∂volume, x ∈ Ioo (0 : ℝ) edge →
        ‖gamma x - (Real.log |x| : ℂ) * k‖ ≤ budget := by
  let test : SchwartzMap ℝ ℂ := k • plateau
  let cotest : BurnolL2 := test.toLp 2 volume
  let cotestFrequencyLog := logSchwartzL2 (𝓕⁻ test)
  let difference := v - cotest
  let actedDifference := gamma - wholeConductorTest test
  have inverseCotest : fourierL2.symm cotest = (𝓕⁻ test).toLp 2 volume := by
    apply fourierL2.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    change test.toLp 2 volume = 𝓕 ((𝓕⁻ test).toLp 2 volume)
    rw [SchwartzMap.toLp_fourier_eq, FourierTransform.fourier_fourierInv_eq]
  have logInverse : LogPair (fourierL2.symm cotest) cotestFrequencyLog := by
    rw [inverseCotest]
    exact original_log_schwartz_domain _
  have testSource : GammaPair cotest (wholeConductorTest test) :=
    gamma_pair_of_log_pairs _ _ _ (original_log_schwartz_domain test) logInverse
  have differenceSource : GammaPair difference actedDifference := by
    intro cot
    change inner ℂ (wholeConductorTest cot) (v - cotest) =
      inner ℂ (cot.toLp 2 volume) (gamma - wholeConductorTest test)
    simp only [inner_sub_right, source cot, testSource cot]
  have testValue (x : ℝ) (inside : |x| < q) : test x = k := by
    change k * plateau x = k
    rw [plateau_one x inside, mul_one]
  have differenceGap : ∀ᵐ x : ℝ ∂volume, |x| < q → difference x = 0 := by
    filter_upwards [constant, Lp.coeFn_sub v cotest, test.coeFn_toLp 2 volume] with
      x native subtract testRead inside
    change (v - cotest) x = v x - cotest x at subtract
    change cotest x = test x at testRead
    exact subtract.trans (by rw [native inside, testRead, testValue x inside, sub_self])
  obtain ⟨gapBound, gapRead⟩ :=
    actual_original_q_gap_Gamma_local_source difference actedDifference differenceSource differenceGap
  let gapBudget := (1/2 : ℝ) * 41 * (∫ y : ℝ, (1 + |y|)⁻¹ * ‖difference y‖)
  let fourierBudget := ∫ y : ℝ, ‖cotestFrequencyLog y‖
  have fourierRaw := fourier_l2_raw cotestFrequencyLog
    (log_schwartz_integrable (𝓕⁻ test))
  have fourierBound (x : ℝ) : ‖𝓕 (cotestFrequencyLog : ℝ → ℂ) x‖ ≤ fourierBudget := by
    rw [Real.fourier_eq]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) (cotestFrequencyLog : ℝ → ℂ) x
  refine ⟨gapBudget + fourierBudget, ?_, ?_⟩
  · dsimp [gapBudget, fourierBudget]
    exact add_nonneg (mul_nonneg (by norm_num) (integral_nonneg (fun _ => by positivity)))
      (integral_nonneg fun _ => norm_nonneg _)
  · filter_upwards [gapRead, Lp.coeFn_sub gamma (wholeConductorTest test),
      Lp.coeFn_add (logSchwartzL2 test) (F cotestFrequencyLog),
      original_log_schwartz_raw test, fourierRaw] with x read subtract add logged fourier inside
    have readDifference : actedDifference x = gamma x - (wholeConductorTest test) x := subtract
    have readTest : wholeConductorTest test x =
        (Real.log |x| : ℂ) * k + 𝓕 (cotestFrequencyLog : ℝ → ℂ) x := by
      change (logSchwartzL2 test + F cotestFrequencyLog) x = _
      change (logSchwartzL2 test + F cotestFrequencyLog) x =
        logSchwartzL2 test x + F cotestFrequencyLog x at add
      rw [add, logged, fourier, testValue x (by rw [abs_of_pos inside.1]; linarith [inside.2])]
    have actual : gamma x - (Real.log |x| : ℂ) * k =
        actedDifference x + 𝓕 (cotestFrequencyLog : ℝ → ℂ) x := by
      rw [readDifference, readTest]
      ring
    rw [actual]
    exact (norm_add_le _ _).trans (add_le_add
      (by rw [read inside]; exact gapBound x ⟨inside.1.le, inside.2.le⟩) (fourierBound x))

private theorem seed_origin_bound :
    ∃ budget : ℝ, 0 ≤ budget ∧
      ∀ᵐ x : ℝ ∂volume, 0 < |x| → |x| < edge →
        ‖actualGammaSeed x‖ ≤ |Real.log (|x|)| + budget := by
  have seedConstant : ∀ᵐ x : ℝ ∂volume, |x| < q → ConstantDual.seed x = 1 := by
    filter_upwards [ConstantDual.seed_coeFn] with x read inside
    rw [read, ConstantDual.seedRaw, if_pos inside.le]
  obtain ⟨budget, nonnegative, positive⟩ := actual_constant_gap_gamma_origin
    ConstantDual.seed actualGammaSeed 1 actual_gamma_seed_source seedConstant
  have reflected := Lp.coeFn_compMeasurePreserving actualGammaSeed negMeasurePreserving
  change (reflectL2 actualGammaSeed : ℝ → ℂ) =ᵐ[volume] fun x => actualGammaSeed (-x) at reflected
  rw [actual_gamma_seed_even] at reflected
  refine ⟨budget, nonnegative, ?_⟩
  filter_upwards [positive, negMeasurePreserving.quasiMeasurePreserving.ae positive, reflected]
    with x onPos onNeg even nonzero near
  have source : ‖actualGammaSeed x - (Real.log |x| : ℂ)‖ ≤ budget := by
    rcases lt_trichotomy x 0 with neg | zero | pos
    · have nx : -x ∈ Ioo (0 : ℝ) edge :=
        ⟨neg_pos.mpr neg, by simpa only [abs_of_neg neg] using near⟩
      have negRead := onNeg nx
      rwa [abs_neg, ← even, mul_one] at negRead
    · simp [zero] at nonzero
    · have posRead := onPos ⟨pos, by simpa only [abs_of_pos pos] using near⟩
      rwa [mul_one] at posRead
  calc
    ‖actualGammaSeed x‖ = ‖(Real.log |x| : ℂ) +
        (actualGammaSeed x - (Real.log |x| : ℂ))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ |Real.log (|x|)| + budget := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (le_refl _) source

private theorem origin_log_bound (y : ℝ) (positive : 0 < y) (small : y ≤ 1) :
    |Real.log y| ≤ 8 * y ^ (-1/8 : ℝ) := by
  have power := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (-1/8 : ℝ))
  rw [Real.log_rpow positive] at power
  rw [abs_of_nonpos (Real.log_nonpos positive.le small)]
  linarith

private theorem actual_gamma_seed_position_log_domain :
    MemLp (fun x : ℝ => (Real.log |x| : ℂ) * actualGammaSeed x) 2 volume := by
  obtain ⟨budget, nonnegative, origin⟩ := seed_origin_bound
  have envelope : MemLp (kGammaFourierPaid% powerEnvelopeRaw) 2 volume :=
    (Lp.memLp (kGammaFourierPaid% powerEnvelopeL2)).ae_eq (kGammaFourierPaid% envelope_raw)
  let price := 64 + 8 * budget + 4
  have dominate := (envelope.norm.const_mul price).add
    ((Lp.memLp actualGammaSeed).norm.const_mul |Real.log edge|)
  apply dominate.of_le ((by fun_prop : Measurable (fun x : ℝ => (Real.log |x| : ℂ))).mul
    (Lp.stronglyMeasurable actualGammaSeed).measurable).aestronglyMeasurable
  filter_upwards [origin, actual_original_gamma_seed_complete_exterior, volume.ae_ne (0 : ℝ)]
    with x originRead exterior nonzero
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have envelopeBound := (kGammaFourierPaid% envelope_norm) x nonzero
  change (if |x| ≤ 1 then |x| ^ (-1/4 : ℝ) else |x| ^ (-3/4 : ℝ)) ≤ _ at envelopeBound
  change ‖(Real.log |x| : ℂ) * actualGammaSeed x‖ ≤
    ‖price * ‖(kGammaFourierPaid% powerEnvelopeRaw) x‖ +
      |Real.log edge| * ‖actualGammaSeed x‖‖
  have priceNonnegative : 0 ≤ price := by dsimp [price]; positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (add_nonneg (mul_nonneg priceNonnegative (norm_nonneg _)) (by positivity))]
  by_cases small : |x| ≤ 1
  · by_cases near : |x| < edge
    · have logBound := origin_log_bound |x| positive small
      have originBound := originRead positive near
      have powerAtLeastOne : 1 ≤ |x| ^ (-1/8 : ℝ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos positive small (by norm_num)
      have squared : (|x| ^ (-1/8 : ℝ)) ^ 2 = |x| ^ (-1/4 : ℝ) := by
        rw [← Real.rpow_two (|x| ^ (-1/8 : ℝ)), ← Real.rpow_mul positive.le]
        norm_num
      have paidPower : |x| ^ (-1/4 : ℝ) ≤ ‖(kGammaFourierPaid% powerEnvelopeRaw) x‖ := by
        simpa only [if_pos small] using envelopeBound
      calc
        |Real.log (|x|)| * ‖actualGammaSeed x‖ ≤
            (8 * |x| ^ (-1/8 : ℝ)) * (8 * |x| ^ (-1/8 : ℝ) + budget) :=
          mul_le_mul logBound (originBound.trans (add_le_add logBound (le_refl _)))
            (norm_nonneg _) (by positivity)
        _ ≤ price * |x| ^ (-1/4 : ℝ) := by
          rw [← squared]
          dsimp [price]
          nlinarith [sq_nonneg (|x| ^ (-1/8 : ℝ)), mul_nonneg nonnegative
            (show 0 ≤ (|x| ^ (-1/8 : ℝ)) ^ 2 - |x| ^ (-1/8 : ℝ) by
              nlinarith [sq_nonneg (|x| ^ (-1/8 : ℝ) - 1)])]
        _ ≤ _ := (mul_le_mul_of_nonneg_left paidPower priceNonnegative).trans
          (le_add_of_nonneg_right (by positivity))
    · have lower := Real.log_le_log (by norm_num : 0 < edge) (le_of_not_gt near)
      have upper := Real.log_nonpos positive.le small
      have collar : |Real.log (|x|)| ≤ |Real.log edge| := by
        rw [abs_of_nonpos upper]
        linarith [neg_abs_le (Real.log edge)]
      exact (mul_le_mul_of_nonneg_right collar (norm_nonneg _)).trans
        (le_add_of_nonneg_left (mul_nonneg priceNonnegative (norm_nonneg _)))
  · have large : 1 < |x| := lt_of_not_ge small
    have inverseBound : ‖actualGammaSeed x‖ ≤ (1/2 : ℝ) / |x| := by
      rw [exterior (by linarith)]
      simpa only [actualGammaSeedExteriorRaw, abs_abs] using
        actual_gamma_seed_exterior_inverse_bound |x| (by linarith)
    have powerOrder : |x| ^ (-1/4 : ℝ) ≤ |x| ^ (1/4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le large.le (by norm_num)
    have logBound : |Real.log (|x|)| ≤ 8 * |x| ^ (1/4 : ℝ) :=
      ((kGammaFourierPaid% log_power_bound) |x| positive).trans (by linarith)
    have product : |x| ^ (1/4 : ℝ) * |x|⁻¹ = |x| ^ (-3/4 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add positive]
      norm_num
    have paidPower : |x| ^ (-3/4 : ℝ) ≤ ‖(kGammaFourierPaid% powerEnvelopeRaw) x‖ := by
      simpa only [if_neg small] using envelopeBound
    calc
      |Real.log (|x|)| * ‖actualGammaSeed x‖ ≤
          (8 * |x| ^ (1/4 : ℝ)) * ((1/2 : ℝ) / |x|) :=
        mul_le_mul logBound inverseBound (norm_nonneg _) (by positivity)
      _ = 4 * |x| ^ (-3/4 : ℝ) := by
        rw [← product, show (1/2 : ℝ) / |x| = (1/2 : ℝ) * |x|⁻¹ from div_eq_mul_inv _ _]
        ring
      _ ≤ price * ‖(kGammaFourierPaid% powerEnvelopeRaw) x‖ :=
        mul_le_mul (by dsimp [price]; linarith) paidPower (by positivity) priceNonnegative
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

def actualGammaSeedPositionLog : BurnolL2 :=
  actual_gamma_seed_position_log_domain.toLp (fun x => (Real.log |x| : ℂ) * actualGammaSeed x)

theorem actual_gamma_seed_position_log : LogPair actualGammaSeed actualGammaSeedPositionLog :=
  actual_gamma_seed_position_log_domain.coeFn_toLp

end
end OriginalGamma.Source.KGamma.Iterated
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
