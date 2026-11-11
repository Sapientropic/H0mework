import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.NormNum.RealSqrt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.Isometry
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.L2Raw
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantForward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContinuousChannels
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SeedCounting
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SmallScaleLog
import H0mework.Arithmetic.TruncatedFourier.ActualBridge
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.ForwardLogStep
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalGamma.Source.FiniteLogCounting
open OriginalGamma.Source.CountingQuadratic OriginalGamma.Source.CountingQuadraticLimit
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private def discreteClock (N : ℕ) : ℝ := (harmonic (N - 1) : ℝ) - Real.log (N : ℝ)

private theorem discrete_clock_tendsto : Tendsto discreteClock atTop (𝓝 Real.eulerMascheroniConstant) := by
  have native := Real.tendsto_eulerMascheroniSeq.comp (tendsto_sub_atTop_nat 1)
  apply native.congr'
  filter_upwards [eventually_ge_atTop 1] with N after
  simp only [discreteClock, Function.comp_apply, Real.eulerMascheroniSeq]
  have same : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast Nat.sub_add_cancel after
  rw [same]

private theorem clock_order (N R : ℕ) (positive : 0 < N) (ordered : N ≤ R) :
    0 ≤ discreteClock R - discreteClock N ∧ discreteClock R - discreteClock N ≤ (N : ℝ)⁻¹ := by
  have first : discreteClock N = Real.eulerMascheroniSeq (N - 1) := by
    unfold discreteClock Real.eulerMascheroniSeq
    have same : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast Nat.sub_add_cancel positive
    rw [same]
  have second : discreteClock R = Real.eulerMascheroniSeq (R - 1) := by
    unfold discreteClock Real.eulerMascheroniSeq
    have same : ((R - 1 : ℕ) : ℝ) + 1 = R := by exact_mod_cast Nat.sub_add_cancel (positive.trans_le ordered)
    rw [same]
  have monotone : discreteClock N ≤ discreteClock R := by
    rw [first, second]
    exact Real.strictMono_eulerMascheroniSeq.monotone (Nat.sub_le_sub_right ordered 1)
  have upper : discreteClock R ≤ Real.eulerMascheroniConstant := by
    rw [second]
    exact (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant _).le
  have lower : Real.eulerMascheroniConstant - discreteClock N ≤ (N : ℝ)⁻¹ := by
    have source := (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N).le
    rw [Real.eulerMascheroniSeq', if_neg positive.ne'] at source
    have step : harmonic N = harmonic (N - 1) + (N : ℚ)⁻¹ := by
      simpa only [Nat.sub_add_cancel positive] using harmonic_succ (N - 1)
    rw [step] at source
    push_cast at source
    unfold discreteClock
    linarith
  exact ⟨sub_nonneg.mpr monotone, by linarith⟩

private def forwardRaw (N : ℕ) (x : ℝ) : ℂ :=
  if x = 0 then 0 else
    if 4 * |x| < (N : ℝ) then
      (discreteClock N - (harmonic (⌈4 * |x|⌉₊ - 1) : ℝ) + Real.log (4 * |x|) : ℝ)
    else 0

private def wholeForwardRaw (x : ℝ) : ℂ :=
  if x = 0 then 0 else
    (Real.eulerMascheroniConstant - (harmonic (⌈4 * |x|⌉₊ - 1) : ℝ) + Real.log (4 * |x|) : ℝ)

private def channelRaw (a x : ℝ) : ℂ :=
  (a : ℂ)⁻¹ * ConstantDual.seedRaw (x / a)

private theorem forward_channel_raw (a : ℝ) (positive : 0 < a) :
    (ContinuousChannels.channel (-1) a ConstantDual.seed : ℝ → ℂ) =ᵐ[volume] channelRaw a := by
  have root : Real.exp (-Real.log a / 2) = (Real.sqrt a)⁻¹ := by
    rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log positive]
  have coefficient : (Real.sqrt a : ℂ)⁻¹ * (Real.sqrt a : ℂ)⁻¹ = (a : ℂ)⁻¹ := by
    rw [← mul_inv, ← sq, ← Complex.ofReal_pow, Real.sq_sqrt positive.le]
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (inv_ne_zero positive.ne')).ae ConstantDual.seed_coeFn
  filter_upwards [original_channel_raw (-1) a ConstantDual.seed, moved] with x original actual
  rw [original]
  simp only [OriginalGamma.Source.FiniteLogCounting.channelRaw, neg_one_mul]
  rw [Real.exp_neg, Real.exp_log positive, root, Complex.ofReal_inv, coefficient]
  simp only [smul_eq_mul] at actual
  unfold channelRaw
  rw [show x / a = a⁻¹ * x by ring, actual]

private theorem channel_raw_measurable : Measurable (fun p : ℝ × ℝ => channelRaw p.1 p.2) := by
  unfold channelRaw
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ)⁻¹)).mul
    (ConstantDual.seedRaw_measurable.comp (by fun_prop))

private theorem normalization_raw (N : ℕ) :
    ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel (-1) a ConstantDual.seed) : BurnolL2) =ᵐ[volume]
      fun x : ℝ => ∫ a : ℝ in Ioc 0 (N : ℝ), channelRaw a x := by
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict (Ioc 0 (N : ℝ))) _
    (ContinuousChannels.channel_integrable (-1) N ConstantDual.seed) _ channel_raw_measurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  exact forward_channel_raw a inside.1


private theorem channel_raw_indicator (a x : ℝ) (positive : 0 < a) :
    channelRaw a x = (Ici (4 * |x|)).indicator (fun t : ℝ => (t : ℂ)⁻¹) a := by
  have incidence : |x / a| ≤ q ↔ 4 * |x| ≤ a := by
    rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]
    constructor <;> intro inside <;> linarith
  unfold channelRaw ConstantDual.seedRaw
  by_cases inside : 4 * |x| ≤ a
  · rw [if_pos (incidence.mpr inside), mul_one, indicator_of_mem (show a ∈ Ici (4 * |x|) from inside)]
  · rw [if_neg (fun h => inside (incidence.mp h)), mul_zero, indicator_of_notMem (show a ∉ Ici (4 * |x|) from inside)]

private theorem normalization_scalar (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    (∫ a : ℝ in Ioc 0 (N : ℝ), channelRaw a x) =
      if 4 * |x| < (N : ℝ) then (Real.log (N : ℝ) - Real.log (4 * |x|) : ℂ) else 0 := by
  have yPositive : 0 < 4 * |x| := mul_pos (by norm_num) (abs_pos.mpr nonzero)
  have same : (fun a : ℝ => channelRaw a x) =ᵐ[volume.restrict (Ioc 0 (N : ℝ))]
      (Ici (4 * |x|)).indicator (fun a : ℝ => (a : ℂ)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
    exact channel_raw_indicator a x inside.1
  rw [integral_congr_ae same, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have intersection : Ici (4 * |x|) ∩ Ioc 0 (N : ℝ) = Icc (4 * |x|) (N : ℝ) := by
    ext a
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨lower, positive, upper⟩
      exact ⟨lower, upper⟩
    · rintro ⟨lower, upper⟩
      exact ⟨lower, yPositive.trans_le lower, upper⟩
  rw [intersection, integral_Icc_eq_integral_Ioc]
  by_cases included : 4 * |x| < (N : ℝ)
  · rw [if_pos included]
    simp only [← Complex.ofReal_inv]
    rw [integral_complex_ofReal, ← intervalIntegral.integral_of_le included.le,
      integral_inv_of_pos yPositive (yPositive.trans included), Real.log_div
        (yPositive.trans included).ne' yPositive.ne', Complex.ofReal_sub]
  · rw [if_neg included, Ioc_eq_empty_of_le (not_lt.mp included)]
    simp

private theorem harmonic_inverse_sum (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ)⁻¹) = (harmonic (N - 1) : ℂ) := by
  have interval : Finset.Ico 1 N = Finset.Icc 1 (N - 1) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [interval, harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro n inside
  simp only [Rat.cast_inv, Rat.cast_natCast]

private theorem integer_scalar (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    (∑ n ∈ Finset.Ico 1 N, channelRaw n x) =
      if 4 * |x| < (N : ℝ) then
        (harmonic (N - 1) : ℂ) - (harmonic (⌈4 * |x|⌉₊ - 1) : ℂ) else 0 := by
  have yPositive : 0 < 4 * |x| := mul_pos (by norm_num) (abs_pos.mpr nonzero)
  have lower : 1 ≤ ⌈4 * |x|⌉₊ := Nat.ceil_pos.mpr yPositive
  have terms (n : ℕ) (inside : n ∈ Finset.Ico 1 N) :
      channelRaw n x = if ⌈4 * |x|⌉₊ ≤ n then (n : ℂ)⁻¹ else 0 := by
    rw [channel_raw_indicator n x (by exact_mod_cast (Finset.mem_Ico.mp inside).1)]
    by_cases active : ⌈4 * |x|⌉₊ ≤ n
    · rw [indicator_of_mem (show (n : ℝ) ∈ Ici (4 * |x|) from Nat.ceil_le.mp active), if_pos active]
      simp only [Complex.ofReal_natCast]
    · rw [indicator_of_notMem (show (n : ℝ) ∉ Ici (4 * |x|) from fun h => active (Nat.ceil_le.mpr h)), if_neg active]
  rw [Finset.sum_congr rfl terms, ← Finset.sum_filter]
  have indices : (Finset.Ico 1 N).filter (fun n : ℕ => ⌈4 * |x|⌉₊ ≤ n) = Finset.Ico ⌈4 * |x|⌉₊ N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [indices]
  by_cases included : 4 * |x| < (N : ℝ)
  · rw [if_pos included]
    have above : ⌈4 * |x|⌉₊ ≤ N := Nat.ceil_le.mpr included.le
    have positiveN : 1 ≤ N := lower.trans above
    have full := harmonic_inverse_sum N
    have head := harmonic_inverse_sum ⌈4 * |x|⌉₊
    rw [Finset.sum_Ico_eq_sub _ positiveN] at full
    rw [Finset.sum_Ico_eq_sub _ lower] at head
    rw [Finset.sum_Ico_eq_sub _ above]
    linear_combination full - head
  · rw [if_neg included, Finset.Ico_eq_empty_of_le]
    · simp
    · have realBound : (N : ℝ) ≤ ⌈4 * |x|⌉₊ := (not_lt.mp included).trans (Nat.le_ceil _)
      exact_mod_cast realBound

private theorem finite_forward_raw (N : ℕ) :
    (CountingDual.sourceCLM N ConstantDual.seed : ℝ → ℂ) =ᵐ[volume] forwardRaw N := by
  have allRows : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      ContinuousChannels.channel (-1) n ConstantDual.seed x = channelRaw n x := by
    apply ae_all_iff.mpr
    intro n
    exact forward_channel_raw n (by exact_mod_cast (Finset.mem_Ico.mp n.property).1)
  have raw := normalization_raw N
  filter_upwards [allRows, raw,
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel (-1) n ConstantDual.seed),
    Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel (-1) n ConstantDual.seed)
      (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel (-1) a ConstantDual.seed),
    volume.ae_ne (0 : ℝ)] with x rows integral sum subtract nonzero
  rw [← original_forward_source]
  unfold countProgramme
  rw [subtract, Pi.sub_apply, sum, integral]
  have integers : (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel (-1) n ConstantDual.seed x) =
      ∑ n ∈ Finset.Ico 1 N, channelRaw n x := by
    apply Finset.sum_congr rfl
    intro n inside
    exact rows ⟨n, inside⟩
  rw [integers, integer_scalar N x nonzero, normalization_scalar N x nonzero]
  unfold forwardRaw
  rw [if_neg nonzero]
  split_ifs
  · unfold discreteClock
    push_cast
    ring
  · ring


private theorem whole_forward_pointwise (x : ℝ) (nonzero : x ≠ 0) :
    Tendsto (fun N : ℕ => forwardRaw N x) atTop (𝓝 (wholeForwardRaw x)) := by
  have native := ((discrete_clock_tendsto.sub_const (harmonic (⌈4 * |x|⌉₊ - 1) : ℝ)).add_const
    (Real.log (4 * |x|)))
  have cast := Complex.continuous_ofReal.tendsto _ |>.comp native
  unfold wholeForwardRaw
  rw [if_neg nonzero]
  apply cast.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (4 * |x|))] with N inside
  simp only [forwardRaw, if_neg nonzero, if_pos inside, Function.comp_apply]

private theorem profile_bound (y δ : ℝ) (positive : 0 < y)
    (nonnegative : 0 ≤ δ) (bound : δ ≤ ((⌈y⌉₊ : ℝ))⁻¹) :
    |δ + Real.log y - Real.log (⌈y⌉₊ : ℝ)| ≤ y⁻¹ := by
  have positiveK : 0 < (⌈y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr positive
  have ceiling : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have near : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one positive.le
  have upperLog : Real.log y ≤ Real.log (⌈y⌉₊ : ℝ) := Real.log_le_log positive ceiling
  have lowerLog := Real.one_sub_inv_le_log_of_pos (div_pos positive positiveK)
  rw [Real.log_div positive.ne' positiveK.ne', inv_div] at lowerLog
  have ratio : (⌈y⌉₊ : ℝ) / y ≤ 1 + y⁻¹ := by
    apply (div_le_iff₀ positive).mpr
    rw [add_mul, one_mul, inv_mul_cancel₀ positive.ne']
    exact near.le
  have inverse : (⌈y⌉₊ : ℝ)⁻¹ ≤ y⁻¹ := inv_le_inv₀ positiveK positive |>.mpr ceiling
  rw [abs_le]
  constructor <;> linarith

private theorem finite_forward_bound (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    ‖forwardRaw N x‖ ≤ if 4 * |x| ≤ 1 then 1 + |Real.log (4 * |x|)| else (4 * |x|)⁻¹ := by
  have yPositive : 0 < 4 * |x| := mul_pos (by norm_num) (abs_pos.mpr nonzero)
  unfold forwardRaw
  rw [if_neg nonzero]
  by_cases included : 4 * |x| < (N : ℝ)
  · rw [if_pos included, Complex.norm_real, Real.norm_eq_abs]
    have positiveN : 0 < N := by exact_mod_cast (yPositive.trans included)
    by_cases small : 4 * |x| ≤ 1
    · rw [if_pos small]
      have one : ⌈4 * |x|⌉₊ = 1 := le_antisymm (Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using small)) (Nat.ceil_pos.mpr yPositive)
      rw [one]
      simp only [Nat.sub_self, harmonic_zero, Rat.cast_zero, sub_zero]
      have bounds := clock_order 1 N (by decide) positiveN
      simp only [discreteClock, Nat.sub_self, harmonic_zero, Rat.cast_zero, Nat.cast_one,
        Real.log_one, sub_self, sub_zero, inv_one] at bounds
      calc
        _ ≤ |discreteClock N| + |Real.log (4 * |x|)| := abs_add_le _ _
        _ ≤ 1 + |Real.log (4 * |x|)| := by
          unfold discreteClock
          rw [abs_of_nonneg bounds.1]
          linarith [bounds.2]
    · rw [if_neg small]
      have kPositive : 0 < ⌈4 * |x|⌉₊ := Nat.ceil_pos.mpr yPositive
      have kBound : ⌈4 * |x|⌉₊ ≤ N := Nat.ceil_le.mpr included.le
      have bounds := clock_order _ N kPositive kBound
      have read : discreteClock N - (harmonic (⌈4 * |x|⌉₊ - 1) : ℝ) + Real.log (4 * |x|) =
          (discreteClock N - discreteClock ⌈4 * |x|⌉₊) + Real.log (4 * |x|) - Real.log (⌈4 * |x|⌉₊ : ℝ) := by
        unfold discreteClock
        ring
      rw [read]
      exact profile_bound _ _ yPositive bounds.1 bounds.2
  · rw [if_neg included, norm_zero]
    split_ifs
    · positivity
    · exact inv_nonneg.mpr yPositive.le


private def powerHead (x : ℝ) : ℂ :=
  (symmetricInterval 1).indicator (fun x : ℝ => ((|x| : ℝ) : ℂ) ^ (-1 / 4 : ℂ)) x

private theorem power_head_memLp : MemLp powerHead 2 volume := by
  have measured : Measurable (fun x : ℝ => ((|x| : ℝ) : ℂ) ^ (-1 / 4 : ℂ)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (Complex.continuousAt_ofReal_cpow_const |x| (-1 / 4 : ℂ)
      (Or.inr (abs_ne_zero.mpr outside))).comp continuous_abs.continuousAt |>.continuousWithinAt
  apply (memLp_indicator_iff_restrict (measurableSet_symmetricInterval 1)).mpr
  apply (memLp_two_iff_integrable_sq_norm measured.aestronglyMeasurable).mpr
  have native := (intervalIntegral.intervalIntegrable_cpow' (r := (-1 / 2 : ℂ))
    (by norm_num) (a := -1) (b := 1)).norm
  have integral : Integrable (fun x : ℝ => ‖(x : ℂ) ^ (-1 / 2 : ℂ)‖)
      (volume.restrict (symmetricInterval 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp native
  apply integral.congr
  filter_upwards [ae_restrict_of_ae (s := symmetricInterval 1) (volume.ae_ne (0 : ℝ))] with x nonzero
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
    show (-1 / 4 : ℂ) = ((-1 / 4 : ℝ) : ℂ) by norm_num]
  simp only [Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  rw [show (-1 / 2 : ℝ) = (-1 / 4 : ℝ) * 2 by ring,
    Real.rpow_mul (abs_nonneg x), Real.rpow_two]

private def powerHeadL2 : BurnolL2 := power_head_memLp.toLp powerHead
private def powerEnvelopeL2 : BurnolL2 := powerHeadL2 + burnolTateReciprocalL2 powerHeadL2

private theorem logarithm_bound (y : ℝ) (positive : 0 < y) :
    |Real.log y| ≤ if y ≤ 1 then 8 * y ^ (-1 / 8 : ℝ) else 8 * y ^ (1 / 8 : ℝ) := by
  by_cases small : y ≤ 1
  · rw [if_pos small, abs_of_nonpos (Real.log_nonpos positive.le small)]
    have source := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (-1 / 8 : ℝ))
    rw [Real.log_rpow positive] at source
    linarith
  · rw [if_neg small, abs_of_nonneg (Real.log_nonneg (le_of_not_ge small))]
    have source := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (1 / 8 : ℝ))
    rw [Real.log_rpow positive] at source
    linarith


private def powerProfile (y : ℝ) : ℝ :=
  if y ≤ 1 then y ^ (-1 / 4 : ℝ) else y ^ (-3 / 4 : ℝ)

private theorem finite_log_bound (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    ‖(Real.log |x| : ℂ) * forwardRaw N x‖ ≤
      (9 * (8 + |Real.log (4 : ℝ)|)) * powerProfile (4 * |x|) := by
  let y : ℝ := 4 * |x|
  let C : ℝ := |Real.log (4 : ℝ)|
  have xpositive : 0 < |x| := abs_pos.mpr nonzero
  have ypositive : 0 < y := mul_pos (by norm_num) xpositive
  have relation : Real.log |x| = Real.log y - Real.log (4 : ℝ) := by
    dsimp [y]
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) xpositive.ne']
    ring
  have factor : |Real.log (|x|)| ≤ |Real.log y| + C := by
    rw [relation]
    exact abs_sub _ _
  have read := finite_forward_bound N x nonzero
  have lnBound := logarithm_bound y ypositive
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply le_trans (mul_le_mul factor read (norm_nonneg _) (by positivity))
  unfold powerProfile
  change (|Real.log y| + C) * (if y ≤ 1 then 1 + |Real.log y| else y⁻¹) ≤
    (9 * (8 + C)) * (if y ≤ 1 then y ^ (-1 / 4 : ℝ) else y ^ (-3 / 4 : ℝ))
  by_cases small : y ≤ 1
  · simp only [if_pos small] at lnBound ⊢
    have unit : 1 ≤ y ^ (-1 / 8 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ypositive small (by norm_num)
    have squared : (y ^ (-1 / 8 : ℝ)) ^ (2 : ℕ) = y ^ (-1 / 4 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul ypositive.le]
      congr 1
      norm_num
    have first : |Real.log y| + C ≤ (8 + C) * y ^ (-1 / 8 : ℝ) := by
      nlinarith [abs_nonneg (Real.log (4 : ℝ))]
    have second : 1 + |Real.log y| ≤ 9 * y ^ (-1 / 8 : ℝ) := by linarith
    calc
      _ ≤ ((8 + C) * y ^ (-1 / 8 : ℝ)) * (9 * y ^ (-1 / 8 : ℝ)) :=
        mul_le_mul first second (by positivity) (by positivity)
      _ = _ := by rw [← squared]; ring
  · simp only [if_neg small] at lnBound ⊢
    have above : 1 ≤ y := le_of_not_ge small
    have unit : 1 ≤ y ^ (1 / 8 : ℝ) := Real.one_le_rpow above (by norm_num)
    have first : |Real.log y| + C ≤ (8 + C) * y ^ (1 / 8 : ℝ) := by
      nlinarith [abs_nonneg (Real.log (4 : ℝ))]
    have product : y ^ (1 / 8 : ℝ) * y⁻¹ = y ^ (-7 / 8 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ypositive]
      congr 1
      norm_num
    have comparison : y ^ (-7 / 8 : ℝ) ≤ y ^ (-3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le above (by norm_num)
    calc
      _ ≤ (8 + C) * y ^ (1 / 8 : ℝ) * y⁻¹ := mul_le_mul_of_nonneg_right first (inv_nonneg.mpr ypositive.le)
      _ = (8 + C) * y ^ (-7 / 8 : ℝ) := by rw [mul_assoc, product]
      _ ≤ (8 + C) * y ^ (-3 / 4 : ℝ) := mul_le_mul_of_nonneg_left comparison (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        dsimp [C]
        nlinarith [abs_nonneg (Real.log (4 : ℝ))]) (Real.rpow_nonneg ypositive.le _)

private def powerEnvelopeRaw (x : ℝ) : ℂ := powerHead x + burnolTateReciprocalRaw powerHead x

private theorem envelope_raw : (powerEnvelopeL2 : ℝ → ℂ) =ᵐ[volume] powerEnvelopeRaw := by
  have source : (powerHeadL2 : ℝ → ℂ) =ᵐ[volume] powerHead := power_head_memLp.coeFn_toLp
  have actual := burnolTateReciprocalL2_coeFn powerHeadL2
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp powerHeadL2) power_head_memLp source
  filter_upwards [Lp.coeFn_add powerHeadL2 (burnolTateReciprocalL2 powerHeadL2), source, actual.trans pulled]
      with x addition first second
  rw [powerEnvelopeL2, addition, Pi.add_apply, first, second]
  rfl

private theorem envelope_norm (x : ℝ) (nonzero : x ≠ 0) : powerProfile |x| ≤ ‖powerEnvelopeRaw x‖ := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have inversePositive : 0 < |x⁻¹| := abs_pos.mpr (inv_ne_zero nonzero)
  unfold powerEnvelopeRaw powerHead burnolTateReciprocalRaw powerProfile
  dsimp only
  by_cases small : |x| ≤ 1
  · rw [if_pos small, indicator_of_mem (show x ∈ symmetricInterval 1 from abs_le.mp small)]
    by_cases inverseSmall : |x|⁻¹ ≤ 1
    · have same : |x| = 1 := le_antisymm small ((inv_le_one₀ positive).mp inverseSmall)
      rw [indicator_of_mem (show x⁻¹ ∈ symmetricInterval 1 from abs_le.mp (by
        simpa only [abs_inv] using inverseSmall)), abs_inv, same]
      norm_num
    · rw [indicator_of_notMem (show x⁻¹ ∉ symmetricInterval 1 from fun h => inverseSmall (by
        rw [← abs_inv]; exact abs_le.mpr h)), mul_zero, add_zero,
        Complex.norm_cpow_eq_rpow_re_of_pos positive]
      norm_num
  · rw [if_neg small, indicator_of_notMem (show x ∉ symmetricInterval 1 from fun h => small (abs_le.mpr h))]
    have inverseSmall : |x|⁻¹ ≤ 1 := (inv_le_one₀ positive).mpr (le_of_not_ge small)
    rw [indicator_of_mem (show x⁻¹ ∈ symmetricInterval 1 from abs_le.mp (by simpa only [abs_inv] using inverseSmall)),
      zero_add, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_abs, abs_inv,
      Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr positive)]
    norm_num
    rw [Real.inv_rpow positive.le, ← Real.rpow_neg positive.le, ← Real.rpow_neg_one,
      ← Real.rpow_add positive]
    norm_num

private def envelopeCoefficient : ℝ := 9 * (8 + |Real.log (4 : ℝ)|)
private def scaledEnvelope : BurnolL2 :=
  (envelopeCoefficient / 2 : ℂ) • burnolMultiplicativeDilation (Real.log 4) powerEnvelopeL2
private def scaledEnvelopeRaw (x : ℝ) : ℂ :=
  (envelopeCoefficient : ℂ) * powerEnvelopeRaw (4 * x)

private theorem scaled_envelope_raw : (scaledEnvelope : ℝ → ℂ) =ᵐ[volume] scaledEnvelopeRaw := by
  have scale : Real.exp (Real.log (4 : ℝ)) = 4 := Real.exp_log (by norm_num)
  have density : Real.exp (Real.log (4 : ℝ) / 2) = 2 := by
    rw [Real.exp_half, scale]
    norm_num
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (Real.exp_ne_zero (Real.log 4))).ae envelope_raw
  filter_upwards [Lp.coeFn_smul (envelopeCoefficient / 2 : ℂ)
      (burnolMultiplicativeDilation (Real.log 4) powerEnvelopeL2),
    burnolMultiplicativeDilation_coeFn (Real.log 4) powerEnvelopeL2, moved]
      with x scalar dilation raw
  change ((envelopeCoefficient / 2 : ℂ) • burnolMultiplicativeDilation (Real.log 4) powerEnvelopeL2 : BurnolL2) x = _
  rw [scalar, Pi.smul_apply, smul_eq_mul, dilation]
  simp only [burnolL2RawNormalizedDilation, smul_eq_mul] at raw ⊢
  rw [raw, scale, density]
  unfold scaledEnvelopeRaw
  push_cast
  ring

private theorem scaled_envelope_memLp : MemLp scaledEnvelopeRaw 2 volume :=
  (Lp.memLp scaledEnvelope).ae_eq scaled_envelope_raw

private def finiteLogRaw (N : ℕ) (x : ℝ) : ℂ := (Real.log |x| : ℂ) * forwardRaw N x
private def wholeLogRaw (x : ℝ) : ℂ := (Real.log |x| : ℂ) * wholeForwardRaw x

private theorem finite_log_pointwise (x : ℝ) (nonzero : x ≠ 0) :
    Tendsto (fun N : ℕ => finiteLogRaw N x) atTop (𝓝 (wholeLogRaw x)) := by
  exact tendsto_const_nhds.mul (whole_forward_pointwise x nonzero)

private theorem finite_log_source_bound (N : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    ‖finiteLogRaw N x‖ ≤ ‖scaledEnvelopeRaw x‖ := by
  have coefficient : 0 ≤ envelopeCoefficient := by unfold envelopeCoefficient; positivity
  have moved := envelope_norm (4 * x) (mul_ne_zero (by norm_num) nonzero)
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at moved
  calc
    _ ≤ envelopeCoefficient * powerProfile (4 * |x|) := finite_log_bound N x nonzero
    _ ≤ envelopeCoefficient * ‖powerEnvelopeRaw (4 * x)‖ := mul_le_mul_of_nonneg_left moved coefficient
    _ = _ := by
      unfold scaledEnvelopeRaw
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg coefficient]

private theorem whole_log_source_bound (x : ℝ) (nonzero : x ≠ 0) :
    ‖wholeLogRaw x‖ ≤ ‖scaledEnvelopeRaw x‖ :=
  le_of_tendsto (finite_log_pointwise x nonzero).norm
    (Eventually.of_forall (fun N => finite_log_source_bound N x nonzero))

private theorem finite_log_memLp (N : ℕ) : MemLp (finiteLogRaw N) 2 volume := by
  have original := (Lp.memLp (CountingDual.sourceCLM N ConstantDual.seed)).ae_eq (finite_forward_raw N)
  apply scaled_envelope_memLp.mono
    ((Complex.measurable_ofReal.comp (Real.measurable_log.comp continuous_abs.measurable)).aestronglyMeasurable.mul original.aestronglyMeasurable)
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  exact finite_log_source_bound N x nonzero

private theorem whole_log_memLp : MemLp wholeLogRaw 2 volume := by
  have count : Measurable (fun x : ℝ => (harmonic (⌈4 * |x|⌉₊ - 1) : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (harmonic (n - 1) : ℝ))).comp
      ((show Measurable (fun x : ℝ => 4 * |x|) from measurable_const.mul continuous_abs.measurable).nat_ceil)
  have whole : Measurable wholeForwardRaw := by
    unfold wholeForwardRaw
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (((measurable_const.sub count).add
        (Real.measurable_log.comp (measurable_const.mul continuous_abs.measurable))).complex_ofReal)
  apply scaled_envelope_memLp.mono
    ((Complex.measurable_ofReal.comp (Real.measurable_log.comp continuous_abs.measurable)).mul whole).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  exact whole_log_source_bound x nonzero

private def finiteLogValue (N : ℕ) : BurnolL2 := (finite_log_memLp N).toLp (finiteLogRaw N)
private def wholeLogValue : BurnolL2 := whole_log_memLp.toLp wholeLogRaw

private theorem finite_log_domain (N : ℕ) : LogPair (CountingDual.sourceCLM N ConstantDual.seed) (finiteLogValue N) := by
  filter_upwards [(finite_log_memLp N).coeFn_toLp, finite_forward_raw N] with x logarithm original
  change ((finite_log_memLp N).toLp (finiteLogRaw N)) x = _
  rw [logarithm, original]
  rfl

private theorem finite_log_value_tendsto : Tendsto finiteLogValue atTop (𝓝 wholeLogValue) := by
  have squareLimit : Tendsto (fun N => ∫ x : ℝ, ‖finiteLogRaw N x - wholeLogRaw x‖ ^ 2) atTop (𝓝 0) := by
    have limit := tendsto_integral_of_dominated_convergence
      (fun x : ℝ => 4 * ‖scaledEnvelopeRaw x‖ ^ 2)
      (F := fun N x => ‖finiteLogRaw N x - wholeLogRaw x‖ ^ 2)
      (f := fun _ => (0 : ℝ))
      (fun N => (((finite_log_memLp N).aestronglyMeasurable.sub whole_log_memLp.aestronglyMeasurable).norm.pow 2))
      (scaled_envelope_memLp.norm.integrable_sq.const_mul 4) ?_ ?_
    · simpa using limit
    · intro N
      filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have bound : ‖finiteLogRaw N x - wholeLogRaw x‖ ≤ 2 * ‖scaledEnvelopeRaw x‖ := by
        calc
          _ ≤ ‖finiteLogRaw N x‖ + ‖wholeLogRaw x‖ := norm_sub_le _ _
          _ ≤ _ := by
            have first := finite_log_source_bound N x nonzero
            have second := whole_log_source_bound x nonzero
            linarith
      nlinarith [sq_nonneg (‖finiteLogRaw N x - wholeLogRaw x‖ - 2 * ‖scaledEnvelopeRaw x‖),
        norm_nonneg (finiteLogRaw N x - wholeLogRaw x), norm_nonneg (scaledEnvelopeRaw x)]
    · filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
      simpa using ((finite_log_pointwise x nonzero).sub (tendsto_const_nhds (x := wholeLogRaw x))).norm.pow 2
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (finiteLogRaw ·) finite_log_memLp wholeLogRaw whole_log_memLp).mpr
  have rootLimit := squareLimit.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
  have limit := ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using rootLimit)
  convert limit using 1
  · ext N
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((finite_log_memLp N).sub whole_log_memLp)]
    simp
  · simp

private def compactLog : BurnolL2 := burnolQuarterZeroExtension
  (SmallScaleLog.logL2 + (Real.log q : ℂ) • intervalConstant q)

private theorem compact_log_raw :
    (compactLog : ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator (fun x => (Real.log |x| : ℂ)) := by
  have localRead : ((SmallScaleLog.logL2 + (Real.log q : ℂ) • intervalConstant q : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval q)]
      fun x => (Real.log |x| : ℂ) := by
    filter_upwards [Lp.coeFn_add SmallScaleLog.logL2 ((Real.log q : ℂ) • intervalConstant q),
      Lp.coeFn_smul (Real.log q : ℂ) (intervalConstant q), SmallScaleLog.log_coeFn,
      intervalConstant_coeFn q, ae_restrict_of_ae (s := symmetricInterval q) (volume.ae_ne (0 : ℝ))]
        with x sumRead scaleRead logarithm constant nonzero
    rw [sumRead]
    change SmallScaleLog.logL2 x + ((Real.log q : ℂ) • intervalConstant q) x = _
    rw [scaleRead]
    change SmallScaleLog.logL2 x + (Real.log q : ℂ) * intervalConstant q x = _
    rw [logarithm, constant, SmallScaleLog.logRaw,
      Real.log_div (abs_ne_zero.mpr nonzero) (by norm_num : q ≠ 0)]
    push_cast
    ring
  have localWhole := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp localRead
  filter_upwards [burnolQuarterZeroExtension_coe
    (SmallScaleLog.logL2 + (Real.log q : ℂ) • intervalConstant q), localWhole] with x extension actual
  unfold compactLog
  rw [extension]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, actual inside]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

private theorem compact_log_domain : LogPair ConstantDual.seed compactLog := by
  filter_upwards [compact_log_raw, ConstantDual.seed_coeFn] with x logarithm seed
  rw [logarithm, seed]
  by_cases inside : |x| ≤ q
  · rw [indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside), ConstantDual.seedRaw, if_pos inside, mul_one]
  · rw [indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h)), ConstantDual.seedRaw, if_neg inside, mul_zero]

private theorem radial_integrable (s : Set ℝ) (hs : MeasurableSet s) (positive : s ⊆ Ioi 0)
    (coefficient : ℝ → ℂ) (measured : Measurable coefficient)
    (weighted : IntegrableOn (fun t => Real.sqrt t * ‖coefficient t‖) s) (value : BurnolL2) :
    IntegrableOn (fun t => coefficient t • radialOrbit t value) s := by
  have regular : AEStronglyMeasurable (fun t => coefficient t • radialOrbit t value) (volume.restrict s) :=
    measured.aestronglyMeasurable.smul
    (((radialOrbit_continuous value).mono positive).aestronglyMeasurable hs)
  apply (integrable_norm_iff regular).mp
  apply (weighted.const_mul (2 * ‖value‖)).congr
  filter_upwards [ae_restrict_mem hs] with t inside
  rw [norm_smul, radialOrbit_norm t (positive inside) value]
  ring

private theorem inv_weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖(t : ℂ)⁻¹‖) (Ioc 0 q) := by
  have original := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := q)
    (by norm_num : -1 < -(1 / 2 : ℝ))).1
  apply original.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos inside.1, Real.sqrt_eq_rpow,
    ← Real.rpow_neg_one, ← Real.rpow_add inside.1]
  congr 1
  norm_num

private def logSynthesis : BurnolL2 →L[ℂ] BurnolL2 :=
  radialSynthesisCLM (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
    (fun t : ℝ => (t : ℂ)⁻¹) (by fun_prop) inv_weighted

private theorem compact_crop (coefficient : ℝ → ℂ) (x : ℝ) :
    (∫ t : ℝ in Ioc 0 q, coefficient t * radialStepRaw t x) = ∫ t : ℝ in Ioc |x| q, coefficient t := by
  have crop : (fun t : ℝ => coefficient t * radialStepRaw t x) =ᵐ[volume.restrict (Ioc 0 q)]
      (Ioc |x| q).indicator coefficient := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne |x|)] with t inside nonzero
    have incidence : |x| ≤ t ↔ t ∈ Ioc |x| q := by
      simp only [mem_Ioc]
      exact ⟨fun h => ⟨lt_of_le_of_ne h nonzero.symm, inside.2⟩, fun h => h.1.le⟩
    by_cases included : t ∈ Ioc |x| q
    · rw [radialStepRaw, if_pos (incidence.mpr included), mul_one, indicator_of_mem included]
    · rw [radialStepRaw, if_neg (fun h => included (incidence.mp h)), mul_zero, indicator_of_notMem included]
  rw [integral_congr_ae crop, setIntegral_indicator measurableSet_Ioc]
  have subset : Ioc |x| q ⊆ Ioc 0 q := fun t ht => ⟨(abs_nonneg x).trans_lt ht.1, ht.2⟩
  rw [inter_eq_right.mpr subset]

private theorem log_synthesis_raw :
    (logSynthesis ConstantDual.seed : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ t : ℝ in Ioc |x| q, (t : ℂ)⁻¹ := by
  have integrable := radial_integrable (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
    (fun t : ℝ => (t : ℂ)⁻¹) (by fun_prop) inv_weighted ConstantDual.seed
  have actual : ((∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ • radialOrbit t ConstantDual.seed : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ t : ℝ in Ioc 0 q, (t : ℂ)⁻¹ * radialStepRaw t x := by
    apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict (Ioc 0 q)) _ integrable
      (fun p : ℝ × ℝ => (p.1 : ℂ)⁻¹ * radialStepRaw p.1 p.2)
      (((by fun_prop : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ)⁻¹))).mul radialStepRaw_measurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
    filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹ (radialStep t), radialStep_coeFn t inside.1] with x scalar step
    change ((t : ℂ)⁻¹ • radialStep t : BurnolL2) x = _
    rw [scalar, Pi.smul_apply, smul_eq_mul, step]
  filter_upwards [actual] with x read
  exact read.trans (compact_crop _ x)

private theorem compact_log_reconstruct :
    compactLog = (Real.log q : ℂ) • ConstantDual.seed - logSynthesis ConstantDual.seed := by
  apply Lp.ext
  filter_upwards [compact_log_raw,
    Lp.coeFn_sub ((Real.log q : ℂ) • ConstantDual.seed) (logSynthesis ConstantDual.seed),
    Lp.coeFn_smul (Real.log q : ℂ) ConstantDual.seed, ConstantDual.seed_coeFn,
    log_synthesis_raw, volume.ae_ne (0 : ℝ)] with x logarithm difference scalar seed integrated nonzero
  rw [logarithm, difference, Pi.sub_apply, scalar, Pi.smul_apply, smul_eq_mul, seed, integrated]
  by_cases inside : |x| ≤ q
  · have primitive : (∫ t : ℝ in Ioc |x| q, (t : ℂ)⁻¹) =
        (Real.log q : ℂ) - (Real.log |x| : ℂ) := by
      rw [← intervalIntegral.integral_of_le inside]
      simp_rw [← Complex.ofReal_inv]
      rw [intervalIntegral.integral_ofReal,
        integral_inv_of_pos (abs_pos.mpr nonzero) (by norm_num : (0 : ℝ) < q),
        Real.log_div (by norm_num : q ≠ 0) (abs_ne_zero.mpr nonzero), Complex.ofReal_sub]
    rw [indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside),
      ConstantDual.seedRaw, if_pos inside, primitive]
    ring
  · rw [indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h)),
      ConstantDual.seedRaw, if_neg inside, mul_zero,
      Ioc_eq_empty_of_le (le_of_not_ge inside)]
    simp

private theorem radial_commute (A : BurnolL2 →L[ℂ] BurnolL2)
    (covariance : ∀ h v, A (burnolMultiplicativeDilation h v) = burnolMultiplicativeDilation h (A v))
    (s : Set ℝ) (hs : MeasurableSet s) (positive : s ⊆ Ioi 0) (coefficient : ℝ → ℂ)
    (measured : Measurable coefficient) (weighted : IntegrableOn (fun t => Real.sqrt t * ‖coefficient t‖) s)
    (value : BurnolL2) :
    A (radialSynthesisCLM s hs positive coefficient measured weighted value) =
      radialSynthesisCLM s hs positive coefficient measured weighted (A value) := by
  rw [radialSynthesisCLM_apply, radialSynthesisCLM_apply,
    ← A.integral_comp_comm (radial_integrable s hs positive coefficient measured weighted value)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_smul, radialOrbit, covariance]


private theorem compact_log_forward_tendsto : Tendsto (fun N : ℕ => CountingDual.sourceCLM N compactLog)
    atTop (𝓝 ((Real.log q : ℂ) • ConstantForward.value - logSynthesis ConstantForward.value)) := by
  have whole := (ConstantForward.original_tendsto.const_smul (Real.log q : ℂ)).sub
    ((logSynthesis.continuous.tendsto ConstantForward.value).comp ConstantForward.original_tendsto)
  apply whole.congr'
  filter_upwards with N
  rw [compact_log_reconstruct, map_sub, map_smul]
  congr 1
  have covariance (h : ℝ) (v : BurnolL2) :
      CountingDual.sourceCLM N (burnolMultiplicativeDilation h v) = burnolMultiplicativeDilation h (CountingDual.sourceCLM N v) :=
    SeedCounting.source_dilation N h v
  simpa only [logSynthesis, Function.comp_apply, CountingDual.sourceCLM_apply] using
    (radial_commute (CountingDual.sourceCLM N) covariance (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
      (fun t : ℝ => (t : ℂ)⁻¹) (by fun_prop) inv_weighted ConstantDual.seed).symm

private theorem log_seed_source (N : ℕ) :
    LogA N ConstantDual.seed = finiteLogValue N - CountingDual.sourceCLM N compactLog := by
  have domain := original_finite_log_domain (-1) N ConstantDual.seed compactLog compact_log_domain
  simp only [original_forward_source, Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, sub_neg_eq_add] at domain
  have native : CountingDual.sourceCLM N compactLog + LogA N ConstantDual.seed = finiteLogValue N := by
    apply Lp.ext
    filter_upwards [domain, finite_log_domain N] with x first second
    exact first.trans second.symm
  rw [← native]
  abel

def logStepValue : BurnolL2 :=
  wholeLogValue - ((Real.log q : ℂ) • ConstantForward.value - logSynthesis ConstantForward.value)

theorem original_log_step_tendsto : Tendsto (fun N : ℕ => LogA N ConstantDual.seed)
    atTop (𝓝 logStepValue) := by
  apply (finite_log_value_tendsto.sub compact_log_forward_tendsto).congr'
  filter_upwards with N
  exact (log_seed_source N).symm


example (N : ℕ) : (CountingDual.sourceCLM N ConstantDual.seed : ℝ → ℂ) =ᵐ[volume] forwardRaw N := finite_forward_raw N

example : ∃ value : BurnolL2, Tendsto (fun N : ℕ => LogA N ConstantDual.seed) atTop (𝓝 value) :=
  ⟨logStepValue, original_log_step_tendsto⟩

end
end OriginalGamma.Source.ForwardLogStep
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
