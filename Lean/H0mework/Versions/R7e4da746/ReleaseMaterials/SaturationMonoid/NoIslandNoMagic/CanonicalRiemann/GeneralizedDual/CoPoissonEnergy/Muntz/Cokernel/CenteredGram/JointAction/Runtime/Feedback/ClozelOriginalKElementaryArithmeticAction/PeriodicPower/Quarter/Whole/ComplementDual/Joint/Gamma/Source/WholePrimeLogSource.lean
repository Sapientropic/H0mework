import Mathlib.Tactic.NormNum.RealSqrt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.Isometry
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.L2Raw
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SmallScaleLog
import H0mework.Arithmetic.TruncatedFourier.ActualBridge
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.WholePrimeLog
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszFiniteSource OriginalRieszSource OriginalRieszSourceGreen
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.CountingQuadraticLimit
open OriginalGamma.Source.CountingQuadratic
noncomputable section
local notation "q" => (1 / 4 : ℝ)
def bSource (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2)

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

private def unitLogHead : BurnolL2 :=
  (2 : ℂ) • burnolMultiplicativeDilation (-Real.log 4)
    (burnolQuarterZeroExtension SmallScaleLog.logL2)

private def unitLogRaw (x : ℝ) : ℂ := if |x| ≤ 1 then (Real.log |x| : ℂ) else 0

private theorem normalized_log_head_raw :
    (burnolQuarterZeroExtension SmallScaleLog.logL2 : ℝ → ℂ) =ᵐ[volume]
      fun x => if |x| ≤ q then (Real.log (|x| / q) : ℂ) else 0 := by
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp SmallScaleLog.log_coeFn
  filter_upwards [burnolQuarterZeroExtension_coe SmallScaleLog.logL2, localRead] with x extension actual
  rw [extension]
  by_cases inside : |x| ≤ q
  · rw [indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside),
      actual (show x ∈ symmetricInterval q from abs_le.mp inside), if_pos inside]
    rfl
  · rw [indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h)), if_neg inside]

private theorem unit_log_head_raw : (unitLogHead : ℝ → ℂ) =ᵐ[volume] unitLogRaw := by
  let h := -Real.log (4 : ℝ)
  have scale : Real.exp h = q := by
    dsimp [h]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have density : Real.exp (h / 2) = 1 / 2 := by
    dsimp [h]
    rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (Real.exp_ne_zero h)).ae normalized_log_head_raw
  filter_upwards [Lp.coeFn_smul (2 : ℂ)
      (burnolMultiplicativeDilation h (burnolQuarterZeroExtension SmallScaleLog.logL2)),
    burnolMultiplicativeDilation_coeFn h (burnolQuarterZeroExtension SmallScaleLog.logL2), moved]
      with x scalar dilation raw
  dsimp only [Pi.smul_apply, smul_eq_mul] at raw
  change ((2 : ℂ) • burnolMultiplicativeDilation h
    (burnolQuarterZeroExtension SmallScaleLog.logL2) : BurnolL2) x = _
  rw [scalar]
  change (2 : ℂ) * burnolMultiplicativeDilation h _ x = _
  rw [dilation]
  simp only [burnolL2RawNormalizedDilation]
  rw [raw, scale, density]
  have incidence : |q * x| ≤ q ↔ |x| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < q)]
    constructor <;> intro bound <;> nlinarith
  have ratio : |q * x| / q = |x| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < q)]
    field_simp
  rw [ratio]
  unfold unitLogRaw
  by_cases inside : |x| ≤ 1
  · rw [if_pos inside, if_pos (incidence.mpr inside)]
    norm_num
    ring
  · rw [if_neg inside, if_neg (fun h => inside (incidence.mp h))]
    norm_num

private def logEnvelope : BurnolL2 := unitLogHead - burnolTateReciprocalL2 unitLogHead
private def logEnvelopeRaw (x : ℝ) : ℂ :=
  if |x| ≤ 1 then (Real.log |x| : ℂ) else ((|x| : ℝ) : ℂ)⁻¹ * (Real.log |x| : ℂ)

private theorem log_envelope_raw : (logEnvelope : ℝ → ℂ) =ᵐ[volume] logEnvelopeRaw := by
  have rawMem := (Lp.memLp unitLogHead).ae_eq unit_log_head_raw
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp unitLogHead) rawMem unit_log_head_raw
  filter_upwards [Lp.coeFn_sub unitLogHead (burnolTateReciprocalL2 unitLogHead), unit_log_head_raw,
    burnolTateReciprocalL2_coeFn unitLogHead, pulled, volume.ae_ne (0 : ℝ)]
      with x difference head reciprocal tail nonzero
  rw [logEnvelope, difference, Pi.sub_apply, head, reciprocal, tail]
  unfold burnolTateReciprocalRaw unitLogRaw logEnvelopeRaw
  rw [abs_inv, Real.log_inv]
  by_cases small : |x| ≤ 1
  · rw [if_pos small, if_pos small]
    by_cases edge : |x| = 1
    · simp [edge]
    · have strict := lt_of_le_of_ne small edge
      have largeInverse : 1 < |x|⁻¹ := by
        rw [inv_eq_one_div]
        exact (lt_div_iff₀ (abs_pos.mpr nonzero)).mpr (by linarith)
      rw [if_neg largeInverse.not_ge, mul_zero, sub_zero]
  · rw [if_neg small, if_neg small]
    have smallInverse : |x|⁻¹ ≤ 1 := by
      rw [inv_eq_one_div]
      exact ((div_le_iff₀ (abs_pos.mpr nonzero)).mpr (by linarith))
    rw [if_pos smallInverse, Complex.ofReal_neg]
    ring

private theorem log_envelope_memLp : MemLp logEnvelopeRaw 2 volume :=
  (Lp.memLp logEnvelope).ae_eq log_envelope_raw

private theorem log_source_bound (x : ℝ) (z : ℂ)
    (bounded : ‖z‖ ≤ 1 ∧ ‖z‖ ≤ q / |x|) :
    ‖(Real.log |x| : ℂ) * z‖ ≤ ‖logEnvelopeRaw x‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases small : |x| ≤ 1
  · rw [logEnvelopeRaw, if_pos small, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) bounded.1
  · rw [logEnvelopeRaw, if_neg small, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    have outer : ‖z‖ ≤ |x|⁻¹ := bounded.2.trans (by
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by norm_num) (abs_nonneg x))
    calc
      _ ≤ |Real.log (|x|)| * |x|⁻¹ := mul_le_mul_of_nonneg_left outer (abs_nonneg _)
      _ = _ := mul_comm _ _

private def finiteLogRaw (N : ℕ) (x : ℝ) : ℂ :=
  (Real.log |x| : ℂ) * ConstantDual.finiteRaw N x
private def wholeLogRaw (x : ℝ) : ℂ := (Real.log |x| : ℂ) * ConstantDual.sawtoothRaw x

private theorem finite_log_memLp (N : ℕ) : MemLp (finiteLogRaw N) 2 volume :=
  log_envelope_memLp.mono (((Complex.measurable_ofReal.comp (Real.measurable_log.comp continuous_abs.measurable)).mul
    (ConstantDual.finite_measurable N)).aestronglyMeasurable)
    (Eventually.of_forall (fun x => log_source_bound x _ (ConstantDual.finite_bounds N x)))
private theorem whole_log_memLp : MemLp wholeLogRaw 2 volume :=
  log_envelope_memLp.mono (((Complex.measurable_ofReal.comp (Real.measurable_log.comp continuous_abs.measurable)).mul
    ConstantDual.sawtooth_measurable).aestronglyMeasurable)
    (Eventually.of_forall (fun x => log_source_bound x _ (ConstantDual.sawtooth_bounds x)))

private def finiteLogValue (N : ℕ) : BurnolL2 := (finite_log_memLp N).toLp (finiteLogRaw N)
private def wholeLogValue : BurnolL2 := whole_log_memLp.toLp wholeLogRaw

private theorem finite_log_domain (N : ℕ) : LogPair (DualSource.source N ConstantDual.seed) (finiteLogValue N) := by
  filter_upwards [(finite_log_memLp N).coeFn_toLp, ConstantDual.finite_coeFn N] with x logarithm original
  change ((finite_log_memLp N).toLp (finiteLogRaw N)) x = _
  rw [logarithm, original]
  rfl

private theorem finite_log_value_tendsto : Tendsto finiteLogValue atTop (𝓝 wholeLogValue) := by
  have squareLimit : Tendsto (fun N => ∫ x : ℝ, ‖finiteLogRaw N x - wholeLogRaw x‖ ^ 2) atTop (𝓝 0) := by
    have limit := tendsto_integral_of_dominated_convergence
      (fun x : ℝ => 4 * ‖logEnvelopeRaw x‖ ^ 2)
      (F := fun N x => ‖finiteLogRaw N x - wholeLogRaw x‖ ^ 2)
      (f := fun _ => (0 : ℝ))
      (fun N => (((finite_log_memLp N).aestronglyMeasurable.sub whole_log_memLp.aestronglyMeasurable).norm.pow 2))
      (log_envelope_memLp.norm.integrable_sq.const_mul 4) ?_ ?_
    · simpa using limit
    · intro N
      filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have bound : ‖finiteLogRaw N x - wholeLogRaw x‖ ≤ 2 * ‖logEnvelopeRaw x‖ := by
        calc
          _ ≤ ‖finiteLogRaw N x‖ + ‖wholeLogRaw x‖ := norm_sub_le _ _
          _ ≤ _ := by
            have first := log_source_bound x (ConstantDual.finiteRaw N x) (ConstantDual.finite_bounds N x)
            have second := log_source_bound x (ConstantDual.sawtoothRaw x) (ConstantDual.sawtooth_bounds x)
            change ‖finiteLogRaw N x‖ ≤ ‖logEnvelopeRaw x‖ at first
            change ‖wholeLogRaw x‖ ≤ ‖logEnvelopeRaw x‖ at second
            linarith
      nlinarith [sq_nonneg (‖finiteLogRaw N x - wholeLogRaw x‖ - 2 * ‖logEnvelopeRaw x‖),
        norm_nonneg (finiteLogRaw N x - wholeLogRaw x), norm_nonneg (logEnvelopeRaw x)]
    · filter_upwards with x
      have pointwise : Tendsto (fun N => finiteLogRaw N x) atTop (𝓝 (wholeLogRaw x)) := by
        apply tendsto_const_nhds.congr'
        exact (ConstantDual.finite_eventually x).mono (fun _ read => by simp only [finiteLogRaw, wholeLogRaw, read])
      simpa using (pointwise.sub (tendsto_const_nhds (x := wholeLogRaw x))).norm.pow 2
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (finiteLogRaw ·) finite_log_memLp wholeLogRaw whole_log_memLp).mpr
  have rootLimit := squareLimit.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
  have limit := ENNReal.continuous_ofReal.tendsto 0 |>.comp (by simpa using rootLimit)
  convert limit using 1
  · ext N
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((finite_log_memLp N).sub whole_log_memLp)]
    simp
  · simp

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

private theorem count_radial (N : ℕ) (s : Set ℝ) (hs : MeasurableSet s) (positive : s ⊆ Ioi 0)
    (coefficient : ℝ → ℂ) (measured : Measurable coefficient)
    (weighted : IntegrableOn (fun t => Real.sqrt t * ‖coefficient t‖) s) (value : BurnolL2) :
    DualSource.source N (radialSynthesisCLM s hs positive coefficient measured weighted value) =
      radialSynthesisCLM s hs positive coefficient measured weighted (DualSource.source N value) := by
  simp_rw [CountingDual.dual_eq_adjoint]
  apply radial_commute
  intro h v
  simp only [← CountingDual.dual_eq_adjoint]
  exact dual_dilation N h v

private theorem compact_log_dual_tendsto : Tendsto (fun N : ℕ => DualSource.source N compactLog)
    atTop (𝓝 ((Real.log q : ℂ) • ConstantDual.value - logSynthesis ConstantDual.value)) := by
  have whole := (ConstantDual.original_tendsto.const_smul (Real.log q : ℂ)).sub
    ((logSynthesis.continuous.tendsto ConstantDual.value).comp ConstantDual.original_tendsto)
  apply whole.congr'
  filter_upwards with N
  rw [compact_log_reconstruct]
  simp only [CountingDual.dual_eq_adjoint, map_sub, map_smul]
  congr 1
  simpa only [logSynthesis, Function.comp_apply, CountingDual.dual_eq_adjoint] using
    (count_radial N (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
      (fun t : ℝ => (t : ℂ)⁻¹) (by fun_prop) inv_weighted ConstantDual.seed).symm

private theorem log_seed_source (N : ℕ) :
    LogD N ConstantDual.seed = DualSource.source N compactLog - finiteLogValue N := by
  have domain := original_finite_log_domain 1 N ConstantDual.seed compactLog compact_log_domain
  have native : DualSource.source N compactLog - LogD N ConstantDual.seed = finiteLogValue N := by
    rw [CountingDual.dual_eq_adjoint]
    change ((CountingDual.sourceCLM N).adjoint compactLog - logProgramme 1 N ConstantDual.seed : BurnolL2) = _
    apply Lp.ext
    filter_upwards [domain, finite_log_domain N] with x first second
    simpa only [original_reverse_source, one_smul, Complex.ofReal_one] using first.trans second.symm
  rw [← native]
  abel

def logStepValue : BurnolL2 :=
  (Real.log q : ℂ) • ConstantDual.value - logSynthesis ConstantDual.value - wholeLogValue

theorem original_log_step_tendsto : Tendsto (fun N : ℕ => LogD N ConstantDual.seed)
    atTop (𝓝 logStepValue) := by
  apply (compact_log_dual_tendsto.sub finite_log_value_tendsto).congr'
  filter_upwards with N
  exact (log_seed_source N).symm

end
end OriginalGamma.Source.WholePrimeLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
