import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Continuity
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Channels
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContinuousChannels
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing
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
namespace OriginalGamma.Source.FiniteLogCounting
open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
open OriginalRieszFinitePairing.CoPoisson.Ward
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

private theorem log_power_bound (a : ℝ) (positive : 0 < a) :
    |Real.log a| ≤ 4 * (a ^ (-(1 / 4 : ℝ)) + a ^ (1 / 4 : ℝ)) := by
  have lower := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (-(1 / 4 : ℝ)))
  have upper := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos positive (1 / 4 : ℝ))
  rw [Real.log_rpow positive] at lower upper
  rw [abs_le]
  constructor <;> nlinarith [Real.rpow_nonneg positive.le (-(1 / 4 : ℝ)),
    Real.rpow_nonneg positive.le (1 / 4 : ℝ)]

private theorem log_root_integrable (upper : ℝ) :
    IntegrableOn (fun a : ℝ => |Real.log a| * a ^ (-(1 / 2 : ℝ))) (Ioc 0 upper) := by
  have first := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := upper)
    (by norm_num : -1 < -(3 / 4 : ℝ))).1
  have second := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := upper)
    (by norm_num : -1 < -(1 / 4 : ℝ))).1
  apply ((first.add second).const_mul 4).mono'
    ((by fun_prop : Measurable (fun a : ℝ => |Real.log a| * a ^ (-(1 / 2 : ℝ)))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg inside.1.le _))]
  calc
    |Real.log a| * a ^ (-(1 / 2 : ℝ)) ≤
        (4 * (a ^ (-(1 / 4 : ℝ)) + a ^ (1 / 4 : ℝ))) * a ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (log_power_bound a inside.1) (Real.rpow_nonneg inside.1.le _)
    _ = _ := by
      rw [mul_assoc, add_mul, ← Real.rpow_add inside.1, ← Real.rpow_add inside.1]
      norm_num

def logChannel (direction a : ℝ) (value : BurnolL2) : BurnolL2 :=
  (Real.log a : ℂ) • ContinuousChannels.channel direction a value

theorem log_channel_integrable (direction upper : ℝ) (value : BurnolL2) :
    IntegrableOn (fun a : ℝ => logChannel direction a value) (Ioc 0 upper) := by
  have regular : ContinuousOn (fun a : ℝ => logChannel direction a value) (Ioi 0) := by
    unfold logChannel ContinuousChannels.channel
    apply (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono (fun _ positive => ne_of_gt positive))).smul
    apply ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.inv₀
      (fun a positive => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr positive).ne')).smul
    exact (burnolMultiplicativeDilation_stronglyContinuous value).comp_continuousOn
      ((Real.continuousOn_log.mono (fun _ positive => ne_of_gt positive)).const_mul direction)
  apply ((log_root_integrable upper).mul_const ‖value‖).mono'
    ((regular.mono (fun _ inside => inside.1)).aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  simp only [logChannel, ContinuousChannels.channel, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg a),
    (burnolMultiplicativeDilation (direction * Real.log a)).norm_map]
  rw [Real.rpow_neg inside.1.le, ← Real.sqrt_eq_rpow]
  exact le_of_eq (mul_assoc _ _ _).symm

def logProgramme (direction : ℝ) (N : ℕ) (value : BurnolL2) : BurnolL2 :=
  (∑ n ∈ Finset.Ico 1 N, logChannel direction n value) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), logChannel direction a value

private theorem log_programme_add (direction : ℝ) (N : ℕ) (left right : BurnolL2) :
    logProgramme direction N (left + right) = logProgramme direction N left + logProgramme direction N right := by
  unfold logProgramme logChannel ContinuousChannels.channel
  simp only [map_add, smul_add, Finset.sum_add_distrib]
  have integrals := integral_add (log_channel_integrable direction N left) (log_channel_integrable direction N right)
  simp only [logChannel, ContinuousChannels.channel] at integrals
  rw [integrals]
  abel

private theorem log_programme_smul (direction : ℝ) (N : ℕ) (scalar : ℂ) (value : BurnolL2) :
    logProgramme direction N (scalar • value) = scalar • logProgramme direction N value := by
  have channel (a : ℝ) : logChannel direction a (scalar • value) = scalar • logChannel direction a value := by
    simp only [logChannel, ContinuousChannels.channel, map_smul, smul_smul]
    module
  unfold logProgramme
  simp_rw [channel, integral_smul, ← Finset.smul_sum]
  exact (smul_sub scalar _ _).symm

def logBudget (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Ico 1 N, |Real.log (n : ℝ)| * (Real.sqrt (n : ℝ))⁻¹) +
    ∫ a : ℝ in Ioc 0 (N : ℝ), |Real.log a| * a ^ (-(1 / 2 : ℝ))

private theorem log_programme_bound (direction : ℝ) (N : ℕ) (value : BurnolL2) :
    ‖logProgramme direction N value‖ ≤ logBudget N * ‖value‖ := by
  have finite (n : ℕ) : ‖logChannel direction n value‖ =
      |Real.log (n : ℝ)| * (Real.sqrt (n : ℝ))⁻¹ * ‖value‖ := by
    simp only [logChannel, ContinuousChannels.channel, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      (burnolMultiplicativeDilation (direction * Real.log (n : ℝ))).norm_map]
    ring
  have continuous : (∫ a : ℝ in Ioc 0 (N : ℝ), ‖logChannel direction a value‖) =
      (∫ a : ℝ in Ioc 0 (N : ℝ), |Real.log a| * a ^ (-(1 / 2 : ℝ))) * ‖value‖ := by
    rw [← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro a inside
    simp only [logChannel, ContinuousChannels.channel, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      (burnolMultiplicativeDilation (direction * Real.log a)).norm_map]
    rw [Real.rpow_neg inside.1.le, ← Real.sqrt_eq_rpow]
    ring
  calc
    _ ≤ ‖∑ n ∈ Finset.Ico 1 N, logChannel direction n value‖ +
      ‖∫ a : ℝ in Ioc 0 (N : ℝ), logChannel direction a value‖ := norm_sub_le _ _
    _ ≤ (∑ n ∈ Finset.Ico 1 N, ‖logChannel direction n value‖) +
      ∫ a : ℝ in Ioc 0 (N : ℝ), ‖logChannel direction a value‖ :=
      add_le_add (norm_sum_le _ _) (norm_integral_le_integral_norm _)
    _ = _ := by simp_rw [finite]; rw [continuous, ← Finset.sum_mul]; unfold logBudget; ring

/-- Only strong values are integrated; the log programme supplies its own bounded linear operator. -/
def logCountingCLM (direction : ℝ) (N : ℕ) : BurnolL2 →L[ℂ] BurnolL2 :=
  ({ toFun := logProgramme direction N
     map_add' := log_programme_add direction N
     map_smul' := log_programme_smul direction N } : BurnolL2 →ₗ[ℂ] BurnolL2).mkContinuous
      (logBudget N) (log_programme_bound direction N)

def LogA (N : ℕ) : BurnolL2 →L[ℂ] BurnolL2 := logCountingCLM (-1) N
def LogD (N : ℕ) : BurnolL2 →L[ℂ] BurnolL2 := logCountingCLM 1 N

@[simp] theorem logCountingCLM_apply (direction : ℝ) (N : ℕ) (value : BurnolL2) :
    logCountingCLM direction N value = logProgramme direction N value := rfl

def countProgramme (direction : ℝ) (N : ℕ) (value : BurnolL2) : BurnolL2 :=
  (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel direction n value) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel direction a value

theorem original_forward_source (N : ℕ) (value : BurnolL2) :
    countProgramme (-1) N value = CountingDual.sourceCLM N value := by
  simp only [countProgramme, CountingDual.sourceCLM_apply, FiniteForcing.source,
    ContinuousChannels.normalization, Channels.sourceChannel, ContinuousChannels.channel, neg_one_mul]

theorem original_reverse_source (N : ℕ) (value : BurnolL2) :
    countProgramme 1 N value = (CountingDual.sourceCLM N).adjoint value := by
  exact CountingDual.dual_eq_adjoint N value

def LogPair (value logValue : BurnolL2) : Prop :=
  (logValue : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (Real.log |x| : ℂ) * value x

def channelRaw (direction a : ℝ) (value : BurnolL2) (x : ℝ) : ℂ :=
  (Real.sqrt a : ℂ)⁻¹ * (Real.exp (direction * Real.log a / 2) : ℂ) *
    value (Real.exp (direction * Real.log a) * x)

theorem original_channel_raw (direction a : ℝ) (value : BurnolL2) :
    (ContinuousChannels.channel direction a value : ℝ → ℂ) =ᵐ[volume] channelRaw direction a value := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt a : ℂ)⁻¹
    (burnolMultiplicativeDilation (direction * Real.log a) value),
    burnolMultiplicativeDilation_coeFn (direction * Real.log a) value] with x scalar actual
  unfold ContinuousChannels.channel
  rw [scalar]
  change (Real.sqrt a : ℂ)⁻¹ * burnolMultiplicativeDilation (direction * Real.log a) value x = _
  rw [actual]
  simp only [channelRaw, burnolL2RawNormalizedDilation]
  ring

private def headLog : BurnolL2 := burnolQuarterZeroExtension
  (SmallScaleLog.logL2 + (Real.log q : ℂ) • intervalConstant q)

private theorem head_log_raw :
    (headLog : ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator (fun x : ℝ => (Real.log |x| : ℂ)) := by
  have localRead : ((SmallScaleLog.logL2 + (Real.log q : ℂ) • intervalConstant q : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq]
      fun x : ℝ => (Real.log |x| : ℂ) := by
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
  unfold headLog
  rw [extension]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, actual inside]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

private theorem log_schwartz_memLp (test : SchwartzMap ℝ ℂ) :
    MemLp (fun x : ℝ => (Real.log |x| : ℂ) * test x) 2 volume := by
  let C := SchwartzMap.seminorm ℝ 0 0 test
  let moment : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) test
  have momentRaw (x : ℝ) : moment x = (x : ℂ) * test x := by
    exact SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) test x
  have positiveC : 0 ≤ C := (norm_nonneg (test 0)).trans (test.norm_le_seminorm ℝ 0)
  have dominate := (((Lp.memLp headLog).norm.const_mul C).add (moment.memLp 2 volume).norm).add
    ((test.memLp 2 volume).norm.const_mul |Real.log q|)
  apply dominate.of_le
    ((by fun_prop : Measurable (fun x : ℝ => (Real.log |x| : ℂ) * test x)).aestronglyMeasurable)
  filter_upwards [head_log_raw] with x head
  dsimp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ C * ‖headLog x‖ + ‖moment x‖ + |Real.log q| * ‖test x‖),
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases inside : x ∈ symmetricInterval q
  · have bound : ‖test x‖ ≤ C := test.norm_le_seminorm ℝ x
    have headNorm : ‖headLog x‖ = |Real.log (|x|)| := by
      rw [head, indicator_of_mem inside, Complex.norm_real, Real.norm_eq_abs]
    calc
      |Real.log (|x|)| * ‖test x‖ ≤ C * ‖headLog x‖ := by rw [headNorm, mul_comm C]; gcongr
      _ ≤ _ := by linarith [norm_nonneg (moment x),
        mul_nonneg (abs_nonneg (Real.log q)) (norm_nonneg (test x))]
  · have outside : q < |x| := lt_of_not_ge (fun bounded => inside (abs_le.mp bounded))
    have positive : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
    have lower := Real.log_le_log (by norm_num : (0 : ℝ) < q) outside.le
    have upper := Real.log_le_sub_one_of_pos positive
    have logBound : |Real.log (|x|)| ≤ |x| + |Real.log q| := by
      rw [abs_le]
      constructor <;> linarith [le_abs_self (Real.log q), neg_abs_le (Real.log q)]
    have momentNorm : ‖moment x‖ = |x| * ‖test x‖ := by
      rw [momentRaw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |Real.log (|x|)| * ‖test x‖ ≤ (|x| + |Real.log q|) * ‖test x‖ := by gcongr
      _ = ‖moment x‖ + |Real.log q| * ‖test x‖ := by rw [momentNorm]; ring
      _ ≤ _ := by linarith [mul_nonneg positiveC (norm_nonneg (headLog x))]

/-- The original compact logarithm and the Schwartz moment generate this cotest's actual log domain. -/
def logSchwartzL2 (test : SchwartzMap ℝ ℂ) : BurnolL2 :=
  (log_schwartz_memLp test).toLp (fun x : ℝ => (Real.log |x| : ℂ) * test x)

theorem original_log_schwartz_raw (test : SchwartzMap ℝ ℂ) :
    (logSchwartzL2 test : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (Real.log |x| : ℂ) * test x :=
  (log_schwartz_memLp test).coeFn_toLp

theorem original_log_schwartz_domain (test : SchwartzMap ℝ ℂ) :
    LogPair (test.toLp 2 volume) (logSchwartzL2 test) := by
  filter_upwards [original_log_schwartz_raw test, test.coeFn_toLp 2 volume] with x logarithm original
  rw [logarithm, original]

private theorem log_channel_raw (direction a : ℝ) (value : BurnolL2) :
    (logChannel direction a value : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (Real.log a : ℂ) * channelRaw direction a value x := by
  filter_upwards [Lp.coeFn_smul (Real.log a : ℂ) (ContinuousChannels.channel direction a value),
    original_channel_raw direction a value] with x scalar raw
  change ((Real.log a : ℂ) • ContinuousChannels.channel direction a value : BurnolL2) x = _
  rw [scalar]
  change (Real.log a : ℂ) * ContinuousChannels.channel direction a value x = _
  rw [raw]

/-- The normalized direction contributes minus direction times log a to the actual multiplication commutator. -/
theorem original_log_channel_domain (direction a : ℝ) (value logValue : BurnolL2)
    (source : LogPair value logValue) :
    LogPair (ContinuousChannels.channel direction a value)
      (ContinuousChannels.channel direction a logValue - (direction : ℂ) • logChannel direction a value) := by
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (Real.exp_ne_zero (direction * Real.log a))).ae source
  change _ =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (ContinuousChannels.channel direction a logValue)
      ((direction : ℂ) • logChannel direction a value),
    Lp.coeFn_smul (direction : ℂ) (logChannel direction a value),
    original_channel_raw direction a logValue, log_channel_raw direction a value,
    original_channel_raw direction a value, moved, volume.ae_ne (0 : ℝ)]
      with x difference scalar logRaw logWeighted raw actual nonzero
  dsimp only [Pi.sub_apply, Pi.smul_apply] at difference scalar actual
  simp only [smul_eq_mul] at actual
  rw [difference, scalar, logRaw, logWeighted, raw]
  simp only [smul_eq_mul, channelRaw]
  rw [actual]
  have logarithm : Real.log |Real.exp (direction * Real.log a) * x| =
      direction * Real.log a + Real.log |x| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      Real.log_mul (Real.exp_ne_zero _) (abs_ne_zero.mpr nonzero), Real.log_exp]
  rw [logarithm]
  push_cast
  ring

private theorem channel_joint_measurable (direction : ℝ) (value : BurnolL2) :
    Measurable (fun p : ℝ × ℝ => channelRaw direction p.1 value p.2) := by
  unfold channelRaw
  exact ((by fun_prop : Measurable (fun p : ℝ × ℝ => (Real.sqrt p.1 : ℂ)⁻¹ *
    (Real.exp (direction * Real.log p.1 / 2) : ℂ)))).mul
    ((Lp.stronglyMeasurable value).measurable.comp (by fun_prop))

private theorem normalization_log_domain (direction upper : ℝ) (value logValue : BurnolL2)
    (source : LogPair value logValue) :
    LogPair (∫ a : ℝ in Ioc 0 upper, ContinuousChannels.channel direction a value)
      ((∫ a : ℝ in Ioc 0 upper, ContinuousChannels.channel direction a logValue) -
        (direction : ℂ) • ∫ a : ℝ in Ioc 0 upper, logChannel direction a value) := by
  let generated : ℝ → BurnolL2 := fun a => ContinuousChannels.channel direction a logValue -
    (direction : ℂ) • logChannel direction a value
  have generatedInt := (ContinuousChannels.channel_integrable direction upper logValue).sub
    ((log_channel_integrable direction upper value).smul (direction : ℂ))
  have integralEq : (∫ a : ℝ in Ioc 0 upper, generated a) =
      (∫ a : ℝ in Ioc 0 upper, ContinuousChannels.channel direction a logValue) -
        (direction : ℂ) • ∫ a : ℝ in Ioc 0 upper, logChannel direction a value := by
    change (∫ a : ℝ in Ioc 0 upper, ContinuousChannels.channel direction a logValue -
      (direction : ℂ) • logChannel direction a value) = _
    calc
      _ = (∫ a : ℝ in Ioc 0 upper, ContinuousChannels.channel direction a logValue) -
          ∫ a : ℝ in Ioc 0 upper, (direction : ℂ) • logChannel direction a value :=
        integral_sub (ContinuousChannels.channel_integrable direction upper logValue)
          ((log_channel_integrable direction upper value).smul (direction : ℂ))
      _ = _ := congrArg ((∫ a : ℝ in Ioc 0 upper, ContinuousChannels.channel direction a logValue) - ·)
        (integral_smul (direction : ℂ) (fun a : ℝ => logChannel direction a value))
  have actualRead := OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc 0 upper)) _ (ContinuousChannels.channel_integrable direction upper value)
    (fun p : ℝ × ℝ => channelRaw direction p.1 value p.2) (channel_joint_measurable direction value)
    (Eventually.of_forall (fun a => original_channel_raw direction a value))
  have logMeasured : Measurable (fun p : ℝ × ℝ => (Real.log |p.2| : ℂ) * channelRaw direction p.1 value p.2) :=
    (by fun_prop : Measurable (fun p : ℝ × ℝ => (Real.log |p.2| : ℂ))).mul
      (channel_joint_measurable direction value)
  have generatedRead := OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc 0 upper)) generated generatedInt
    (fun p : ℝ × ℝ => (Real.log |p.2| : ℂ) * channelRaw direction p.1 value p.2) logMeasured (by
      apply Eventually.of_forall
      intro a
      have domain := original_log_channel_domain direction a value logValue source
      filter_upwards [domain, original_channel_raw direction a value] with x logarithm raw
      exact logarithm.trans (by rw [raw]))
  rw [← integralEq]
  filter_upwards [actualRead, generatedRead] with x actual logarithm
  rw [logarithm, actual, integral_const_mul]

private theorem log_pair_sub (value logValue other logOther : BurnolL2)
    (first : LogPair value logValue) (second : LogPair other logOther) :
    LogPair (value - other) (logValue - logOther) := by
  filter_upwards [first, second, Lp.coeFn_sub value other, Lp.coeFn_sub logValue logOther]
    with x source otherSource raw logRaw
  dsimp only [Pi.sub_apply] at raw logRaw
  rw [logRaw, raw, source, otherSource, mul_sub]

/-- All finite integer logarithms and the entire continuous normalization remain in the source domain. -/
theorem original_finite_log_domain (direction : ℝ) (N : ℕ) (value logValue : BurnolL2)
    (source : LogPair value logValue) :
    LogPair (countProgramme direction N value)
      (countProgramme direction N logValue - (direction : ℂ) • logProgramme direction N value) := by
  let generated : ℕ → BurnolL2 := fun n => ContinuousChannels.channel direction n logValue -
    (direction : ℂ) • logChannel direction n value
  have allRead : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      generated n x = (Real.log |x| : ℂ) * ContinuousChannels.channel direction n value x := by
    apply ae_all_iff.mpr
    intro n
    exact original_log_channel_domain direction n value logValue source
  have finite : LogPair (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel direction n value)
      (∑ n ∈ Finset.Ico 1 N, generated n) := by
    filter_upwards [allRead,
      Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) generated,
      Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel direction n value)]
        with x actual logRaw raw
    rw [logRaw, raw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n inside
    exact actual ⟨n, inside⟩
  have combined := log_pair_sub _ _ _ _ finite (normalization_log_domain direction N value logValue source)
  have equation :
      (∑ n ∈ Finset.Ico 1 N, generated n) -
        ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel direction a logValue) -
          (direction : ℂ) • ∫ a : ℝ in Ioc 0 (N : ℝ), logChannel direction a value) =
      countProgramme direction N logValue - (direction : ℂ) • logProgramme direction N value := by
    simp only [generated, Finset.sum_sub_distrib, ← Finset.smul_sum, countProgramme, logProgramme]
    module
  rw [equation] at combined
  exact combined

end
end OriginalGamma.Source.FiniteLogCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
