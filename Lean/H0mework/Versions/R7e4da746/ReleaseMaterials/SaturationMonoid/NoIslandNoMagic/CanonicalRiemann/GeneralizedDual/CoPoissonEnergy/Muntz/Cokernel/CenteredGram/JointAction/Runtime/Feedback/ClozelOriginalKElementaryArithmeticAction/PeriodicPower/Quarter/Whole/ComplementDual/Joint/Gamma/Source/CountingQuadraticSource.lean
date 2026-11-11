import Mathlib.MeasureTheory.Integral.DominatedConvergence
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Continuity
import H0mework.Arithmetic.SonineProjection.MeanZeroBlock
import H0mework.Versions.R7e4da746.Arithmetic.SonineProjection.ConstructorCompact
import H0mework.Versions.R7e4da746.Arithmetic.SonineProjection.Return
import H0mework.Versions.R7e4da746.Arithmetic.RieszEuler.EdgeRaw
import H0mework.Versions.R7e4da746.Arithmetic.RieszEuler.Scalar
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Trace
import H0mework.Versions.R7e4da746.Arithmetic.RieszForcing.ForcingMeanZero
import H0mework.Versions.R7e4da746.Arithmetic.RieszForcing.ForcingWhole
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingPrimitive
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingTail
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCountingGram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RegularQuadrature
import H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.SourceDerivative
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.RawDerivative
import H0mework.Versions.R7e4da746.Arithmetic.RieszCanonicalRaw.Forcing
import H0mework.Versions.R7e4da746.Arithmetic.RieszCanonicalRaw.RieszSingleFourierSource
import H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.GapTailDilation
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Arithmetic.TruncatedFourier.ActualBridge
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.CountingQuadratic
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszSource OriginalRieszSourceGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)

/-- The same quarter source, transported by its installed physical dilation. -/
def radialStep (t : ℝ) : BurnolL2 :=
  (Real.exp (Real.log (4 * t) / 2) : ℂ) •
    burnolMultiplicativeDilation (-Real.log (4 * t)) ConstantDual.seed

def radialStepRaw (t x : ℝ) : ℂ := if |x| ≤ t then 1 else 0

theorem quarterSeed_norm_sq : ‖ConstantDual.seed‖ ^ 2 = 1 / 2 := by
  have extension : ‖ConstantDual.seed‖ = ‖intervalConstant q‖ := by
    change ‖burnolQuarterZeroExtension (intervalConstant q)‖ = _
    rw [← burnolQuarterZeroExtensionExplicit_is_adjoint]
    exact burnolQuarterZeroExtensionValue_norm _
  rw [extension]
  have actual := congrArg Complex.re (burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q))
  norm_num [← Complex.ofReal_pow] at actual ⊢
  exact actual

theorem radialStep_norm_sq (t : ℝ) (positive : 0 < t) : ‖radialStep t‖ ^ 2 = 2 * t := by
  rw [radialStep, norm_smul, LinearIsometryEquiv.norm_map, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, quarterSeed_norm_sq,
    ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have exponent : (2 : ℝ) * (Real.log (4 * t) / 2) = Real.log (4 * t) := by ring
  rw [exponent, Real.exp_log (by positivity)]
  ring

theorem radialStep_norm (t : ℝ) (positive : 0 < t) : ‖radialStep t‖ = Real.sqrt (2 * t) := by
  have square := radialStep_norm_sq t positive
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * t), Real.sqrt_nonneg (2 * t),
    norm_nonneg (radialStep t)]

theorem radialStep_continuous : ContinuousOn radialStep (Ioi 0) := by
  intro t positive
  change 0 < t at positive
  unfold radialStep
  apply ContinuousAt.continuousWithinAt
  have logarithm : ContinuousAt (fun u : ℝ => Real.log (4 * u)) t :=
    (continuous_const.mul continuous_id).continuousAt.log (ne_of_gt (mul_pos (by norm_num) positive))
  exact ((Complex.continuous_ofReal.continuousAt.comp
      (Real.continuous_exp.continuousAt.comp (logarithm.div_const 2))).smul
    ((burnolMultiplicativeDilation_stronglyContinuous ConstantDual.seed).continuousAt.comp
      logarithm.neg))

theorem radialStep_coeFn (t : ℝ) (positive : 0 < t) :
    (radialStep t : ℝ → ℂ) =ᵐ[volume] radialStepRaw t := by
  let h : ℝ := -Real.log (4 * t)
  have quasi : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  filter_upwards [Lp.coeFn_smul (Real.exp (Real.log (4 * t) / 2) : ℂ)
      (burnolMultiplicativeDilation h ConstantDual.seed),
    burnolMultiplicativeDilation_coeFn h ConstantDual.seed,
    quasi.ae ConstantDual.seed_coeFn] with x scalar dilation source
  rw [radialStep, scalar]
  change (Real.exp (Real.log (4 * t) / 2) : ℂ) *
    burnolMultiplicativeDilation h ConstantDual.seed x = _
  rw [dilation]
  change (Real.exp (Real.log (4 * t) / 2) : ℂ) *
    ((Real.exp (h / 2) : ℂ) * ConstantDual.seed (Real.exp h * x)) = _
  rw [source]
  have density : (Real.exp (Real.log (4 * t) / 2) : ℂ) *
      (Real.exp (h / 2) : ℂ) = 1 := by
    have actual : Real.exp (Real.log (4 * t) / 2) * Real.exp (h / 2) = 1 := by
      rw [← Real.exp_add]
      have cancel : Real.log (4 * t) / 2 + h / 2 = 0 := by dsimp [h]; ring
      rw [cancel, Real.exp_zero]
    exact_mod_cast actual
  have scale : Real.exp h = (4 * t)⁻¹ := by
    change Real.exp (-Real.log (4 * t)) = _
    rw [Real.exp_neg, Real.exp_log (by positivity)]
  have incidence : |Real.exp h * x| ≤ q ↔ |x| ≤ t := by
    rw [abs_mul, abs_of_pos (Real.exp_pos h), scale]
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
    have cancel : q * (4 * t) = t := by ring
    rw [cancel]
  rw [← mul_assoc, density, one_mul, ConstantDual.seedRaw, radialStepRaw]
  by_cases inside : |x| ≤ t
  · rw [if_pos inside, if_pos (incidence.mpr inside)]
  · rw [if_neg inside, if_neg (fun included => inside (incidence.mp included))]

def bRegular (c : BurnolCompletedMellinCoordinate) (t : ℝ) : ℂ :=
  ForcingTail.forcingRemainder c t - Translator.ForcingMeanZero.mean c +
    Constructor.secondReturnRaw c t

def bRegularSlope (c : BurnolCompletedMellinCoordinate) (t : ℝ) : ℂ :=
  RegularQuadrature.forcingSlope c t +
    Constructor.fourierDerivative (burnolRieszReturnRaw c) t

theorem b_regular_synthesis (c : BurnolCompletedMellinCoordinate) (t : ℝ) (positive : 0 < t) :
    burnolRieszSingleFourierSourceRaw c t =
      ForcingPrimitive.leadingCoefficient c * (t : ℂ) ^ (star c.value - 1) + bRegular c t := by
  rw [ForcingPrimitive.original_source_read c t positive]
  unfold bRegular ForcingTail.forcingRemainder ForcingTail.edgeRemainder
  rw [abs_of_pos positive]
  ring

theorem b_regular_hasDerivAt (c : BurnolCompletedMellinCoordinate) (t : ℝ)
    (nonnegative : 0 ≤ t) : HasDerivAt (bRegular c) (bRegularSlope c t) t :=
  ((RegularQuadrature.forcing_derivative c t nonnegative).sub_const _).add
    (Constructor.secondReturnRaw_hasDerivAt c t)

theorem b_regular_slope_continuous (c : BurnolCompletedMellinCoordinate) :
    ContinuousOn (bRegularSlope c) (Icc 0 q) :=
  (RegularQuadrature.forcing_slope_continuous c).add
    (Constructor.fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous c)).continuousOn

theorem b_slope_synthesis (c : BurnolCompletedMellinCoordinate) (t : ℝ) (positive : 0 < t) :
    sourceRawDerivative c t =
      (ForcingPrimitive.leadingCoefficient c * (star c.value - 1)) *
        (t : ℂ) ^ (star c.value - 2) + bRegularSlope c t := by
  have power := (Complex.hasStrictDerivAt_cpow_const
    (c := star c.value - 1) (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal
  have generated := (power.const_mul (ForcingPrimitive.leadingCoefficient c)).add
    (b_regular_hasDerivAt c t positive.le)
  have same : burnolRieszSingleFourierSourceRaw c =ᶠ[𝓝 t]
      fun x => ForcingPrimitive.leadingCoefficient c * (x : ℂ) ^ (star c.value - 1) + bRegular c x := by
    filter_upwards [Ioi_mem_nhds positive] with x hx
    exact b_regular_synthesis c x hx
  have exactDerivative := generated.congr_of_eventuallyEq same
  have slope := (sourceRaw_hasDerivAt c t positive.ne').unique exactDerivative
  convert slope using 1
  have exponent : star c.value - 1 - 1 = star c.value - 2 := by ring
  rw [exponent]
  ring

theorem b_weighted_slope_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => Real.sqrt t * ‖sourceRawDerivative c t‖) (Ioc 0 q) := by
  let a : ℝ := ‖ForcingPrimitive.leadingCoefficient c * (star c.value - 1)‖
  have singular : IntegrableOn (fun t : ℝ => a * t ^ (c.value.re - 3 / 2)) (Ioc 0 q) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [c.rightHalf])).1.const_mul a
  have regular : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖bRegularSlope c t‖) (Ioc 0 q) :=
    ((Real.continuous_sqrt.continuousOn.mul (b_regular_slope_continuous c).norm).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have measurable : AEStronglyMeasurable (fun t : ℝ => Real.sqrt t * ‖sourceRawDerivative c t‖)
      (volume.restrict (Ioc 0 q)) := by
    have actual := (Real.continuous_sqrt.measurable.mul
      (measurable_deriv (burnolRieszSingleFourierSourceRaw c)).norm).aestronglyMeasurable
        (μ := volume.restrict (Ioc 0 q))
    apply actual.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
    dsimp only [Pi.mul_apply]
    rw [(sourceRaw_hasDerivAt c t inside.1.ne').deriv]
  apply Integrable.mono' (singular.add regular) measurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg t) (norm_nonneg _)),
    b_slope_synthesis c t inside.1]
  have weightedPower : Real.sqrt t * ‖(t : ℂ) ^ (star c.value - 2)‖ =
      t ^ (c.value.re - 3 / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.norm_cpow_eq_rpow_re_of_pos inside.1,
      ← Real.rpow_add inside.1]
    congr 1
    norm_num [sub_re, star_def, conj_re]
    ring
  calc
    _ ≤ Real.sqrt t * (‖(ForcingPrimitive.leadingCoefficient c * (star c.value - 1)) *
        (t : ℂ) ^ (star c.value - 2)‖ + ‖bRegularSlope c t‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg t)
    _ = a * t ^ (c.value.re - 3 / 2) + Real.sqrt t * ‖bRegularSlope c t‖ := by
      rw [norm_mul, mul_add, ← mul_assoc, mul_comm (Real.sqrt t) a, mul_assoc, weightedPower]

theorem source_slope_measurable (c : BurnolCompletedMellinCoordinate) :
    Measurable (sourceRawDerivative c) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro t outside
  have nonzero : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
  exact ((((continuousAt_const.mul (Translator.ForcingWhole.raw_continuousAt c nonzero)).add
    (continuousAt_const.mul (Edge.raw_continuous q).continuousAt)).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr nonzero)).add
    (Constructor.fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous c)).continuousAt).continuousWithinAt

theorem radialStep_aestronglyMeasurable (s : Set ℝ) (measurable : MeasurableSet s)
    (positive : s ⊆ Ioi 0) : AEStronglyMeasurable radialStep (volume.restrict s) :=
  (radialStep_continuous.mono positive).aestronglyMeasurable measurable

theorem b_step_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => sourceRawDerivative c t • radialStep t) (Ioc 0 q) := by
  have measurable : AEStronglyMeasurable (fun t : ℝ => sourceRawDerivative c t • radialStep t)
      (volume.restrict (Ioc 0 q)) := (source_slope_measurable c).aestronglyMeasurable.smul
    (radialStep_aestronglyMeasurable (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self)
  apply (integrable_norm_iff measurable).mp
  apply ((b_weighted_slope_integrable c).const_mul (Real.sqrt 2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  rw [norm_smul, radialStep_norm t inside.1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem return_step_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => burnolRieszReturnRawDerivative c t • radialStep t) (Ioc 0 q) := by
  have measurable : AEStronglyMeasurable (fun t : ℝ => burnolRieszReturnRawDerivative c t • radialStep t)
      (volume.restrict (Ioc 0 q)) := (burnolRieszReturnRawDerivative_continuous c).measurable.aestronglyMeasurable.smul
    (radialStep_aestronglyMeasurable (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self)
  have normIntegrable : IntegrableOn (fun t : ℝ =>
      Real.sqrt 2 * (Real.sqrt t * ‖burnolRieszReturnRawDerivative c t‖)) (Ioc 0 q) :=
    (((continuous_const.mul (Real.continuous_sqrt.mul
      (burnolRieszReturnRawDerivative_continuous c).norm)).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  apply (integrable_norm_iff measurable).mp
  apply normIntegrable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t inside
  rw [norm_smul, radialStep_norm t inside.1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem tail_step_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1) • radialStep t) (Ioi q) := by
  have powerContinuous : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1)) (Ioi q) := by
    intro t inside
    exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (lt_trans (by norm_num) inside).ne')).continuousWithinAt
  have measurable : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1) • radialStep t)
      (volume.restrict (Ioi q)) := (powerContinuous.aestronglyMeasurable measurableSet_Ioi).smul
    (radialStep_aestronglyMeasurable _ measurableSet_Ioi (Ioi_subset_Ioi (by norm_num)))
  have powerIntegrable := (integrableOn_Ioi_rpow_of_lt
    (by linarith [c.rightHalf] : -c.value.re - 1 / 2 < -1) (by norm_num : (0 : ℝ) < q)).const_mul
      (Real.sqrt 2)
  apply (integrable_norm_iff measurable).mp
  apply powerIntegrable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t inside
  have positive : 0 < t := lt_trans (by norm_num) inside
  rw [norm_smul, radialStep_norm t positive, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_eq_rpow t, Complex.norm_cpow_eq_rpow_re_of_pos positive]
  have exponent : (-star c.value - 1).re = -c.value.re - 1 := by simp
  rw [exponent]
  have combine : t ^ (-c.value.re - 1) * t ^ (1 / 2 : ℝ) = t ^ (-c.value.re - 1 / 2) := by
    rw [← Real.rpow_add positive]
    congr 1
    ring
  linear_combination -(Real.sqrt 2) * combine

theorem radialStepRaw_measurable :
    Measurable (fun p : ℝ × ℝ => radialStepRaw p.1 p.2) := by
  exact Measurable.ite (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_fst)
    measurable_const measurable_const

private theorem step_integral_raw (s : Set ℝ) (measurableS : MeasurableSet s)
    (positiveS : s ⊆ Ioi 0) (coefficient : ℝ → ℂ) (measurable : Measurable coefficient)
    (integrable : IntegrableOn (fun t => coefficient t • radialStep t) s) :
    ((∫ t in s, coefficient t • radialStep t : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ t in s, coefficient t * radialStepRaw t x := by
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict s) _ integrable
    (fun p : ℝ × ℝ => coefficient p.1 * radialStepRaw p.1 p.2)
    ((measurable.comp measurable_fst).mul radialStepRaw_measurable)
  filter_upwards [ae_restrict_mem measurableS] with t inside
  filter_upwards [Lp.coeFn_smul (coefficient t) (radialStep t),
    radialStep_coeFn t (positiveS inside)] with x scalar source
  rw [scalar, Pi.smul_apply, smul_eq_mul, source]

private theorem compact_step_crop (slope : ℝ → ℂ) (x : ℝ) :
    (∫ t : ℝ in Ioc 0 q, slope t * radialStepRaw t x) = ∫ t : ℝ in Ioc |x| q, slope t := by
  have crop : (fun t : ℝ => slope t * radialStepRaw t x) =ᵐ[volume.restrict (Ioc 0 q)]
      (Ioc |x| q).indicator slope := by
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

def bStepIntegral (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ∫ t : ℝ in Ioc 0 q, sourceRawDerivative c t • radialStep t

theorem bStepIntegral_coeFn (c : BurnolCompletedMellinCoordinate) :
    (bStepIntegral c : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ t : ℝ in Ioc |x| q, sourceRawDerivative c t := by
  have raw := step_integral_raw (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
    (sourceRawDerivative c) (source_slope_measurable c) (b_step_integrable c)
  filter_upwards [raw] with x read
  exact read.trans (compact_step_crop _ x)

theorem b_positive_interval_integral (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (positive : 0 < x) (inside : x ≤ q) :
    (∫ t : ℝ in Ioc x q, sourceRawDerivative c t) =
      burnolRieszSingleFourierSourceRaw c q - burnolRieszSingleFourierSourceRaw c x := by
  rw [← intervalIntegral.integral_of_le inside]
  have derivative : ∀ t ∈ uIcc x q,
      HasDerivAt (burnolRieszSingleFourierSourceRaw c) (sourceRawDerivative c t) t := by
    intro t ht
    rw [uIcc_of_le inside] at ht
    exact sourceRaw_hasDerivAt c t (positive.trans_le ht.1).ne'
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
  have continuous : ContinuousOn (sourceRawDerivative c) (Icc x q) := by
    intro t ht
    have nonzero := (positive.trans_le ht.1).ne'
    exact ((((continuousAt_const.mul (Translator.ForcingWhole.raw_continuousAt c nonzero)).add
      (continuousAt_const.mul (Edge.raw_continuous q).continuousAt)).div
        Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr nonzero)).add
      (Constructor.fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous c)).continuousAt).continuousWithinAt
  exact continuous.intervalIntegrable_of_Icc inside

/-- This reconstructs the original source b with its actual, generally nonzero endpoint beta. -/
theorem original_b_step_reconstruction (c : BurnolCompletedMellinCoordinate) :
    burnolQuarterZeroExtension (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2) =
      Kernel.beta c • ConstantDual.seed - bStepIntegral c := by
  have bRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolRieszSingleFourierSource_ae_raw c)
  apply Lp.ext
  filter_upwards [burnolQuarterZeroExtension_coe (burnolRieszSingleFourierSource c : BurnolQuarterIntervalL2),
    bRead, Lp.coeFn_sub (Kernel.beta c • ConstantDual.seed) (bStepIntegral c),
    Lp.coeFn_smul (Kernel.beta c) ConstantDual.seed, ConstantDual.seed_coeFn,
    bStepIntegral_coeFn c, volume.ae_ne (0 : ℝ)] with x extension b source scalar step integrated nonzero
  rw [source, Pi.sub_apply, scalar, Pi.smul_apply, smul_eq_mul, step, integrated, extension]
  have absolute : burnolRieszSingleFourierSourceRaw c |x| = burnolRieszSingleFourierSourceRaw c x := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, OriginalRieszFinitePairing.source_raw_even]
  by_cases inside : |x| ≤ q
  · rw [indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside),
      b (abs_le.mp inside), ConstantDual.seedRaw, if_pos inside,
      b_positive_interval_integral c |x| (abs_pos.mpr nonzero) inside, absolute]
    unfold Kernel.beta
    ring
  · have empty : Ioc |x| q = ∅ := Ioc_eq_empty_of_le (le_of_not_ge inside)
    rw [indicator_of_notMem (show x ∉ symmetricInterval q from fun hx => inside (abs_le.mpr hx)),
      ConstantDual.seedRaw, if_neg inside, mul_zero, empty]
    simp

def returnStepIntegral (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ∫ t : ℝ in Ioc 0 q, burnolRieszReturnRawDerivative c t • radialStep t

def tailStepIntegral (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ∫ t : ℝ in Ioi q, (t : ℂ) ^ (-star c.value - 1) • radialStep t

theorem returnStepIntegral_coeFn (c : BurnolCompletedMellinCoordinate) :
    (returnStepIntegral c : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ t : ℝ in Ioc |x| q, burnolRieszReturnRawDerivative c t := by
  have raw := step_integral_raw (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
    (burnolRieszReturnRawDerivative c) (burnolRieszReturnRawDerivative_continuous c).measurable
    (return_step_integrable c)
  filter_upwards [raw] with x read
  exact read.trans (compact_step_crop _ x)

private theorem tail_power_measurable (c : BurnolCompletedMellinCoordinate) :
    Measurable (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1)) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro t outside
  have nonzero : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
  exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr nonzero)).continuousWithinAt

private theorem tail_scalar_crop (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    (∫ t : ℝ in Ioi q, (t : ℂ) ^ (-star c.value - 1) * radialStepRaw t x) =
      ((max q |x| : ℝ) : ℂ) ^ (-star c.value) / star c.value := by
  have crop : (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1) * radialStepRaw t x) =ᵐ[
      volume.restrict (Ioi q)] (Ioi |x|).indicator (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1)) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne |x|)] with t nonzero
    have incidence : |x| ≤ t ↔ t ∈ Ioi |x| :=
      ⟨fun h => lt_of_le_of_ne h nonzero.symm, fun h => h.le⟩
    by_cases inside : t ∈ Ioi |x|
    · rw [radialStepRaw, if_pos (incidence.mpr inside), mul_one, indicator_of_mem inside]
    · rw [radialStepRaw, if_neg (fun h => inside (incidence.mp h)), mul_zero, indicator_of_notMem inside]
  have decay : (-star c.value - 1).re < -1 := by
    simp only [sub_re, neg_re, star_def, conj_re, one_re]
    linarith [c.rightHalf]
  rw [integral_congr_ae crop, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
    integral_Ioi_cpow_of_lt decay (lt_of_lt_of_le (by norm_num : (0 : ℝ) < q) (le_max_left q |x|)),
    sub_add_cancel, neg_div_neg_eq]

theorem tailStepIntegral_coeFn (c : BurnolCompletedMellinCoordinate) :
    (tailStepIntegral c : ℝ → ℂ) =ᵐ[volume]
      fun x => ((max q |x| : ℝ) : ℂ) ^ (-star c.value) / star c.value := by
  have raw := step_integral_raw (Ioi q) measurableSet_Ioi (Ioi_subset_Ioi (by norm_num))
    (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1)) (tail_power_measurable c) (tail_step_integrable c)
  filter_upwards [raw] with x read
  exact read.trans (tail_scalar_crop c x)

theorem A_original_gap (c : BurnolCompletedMellinCoordinate) :
    Kernel.A c = GapEuler.gapMean q c + burnolRieszReturnRaw c q -
      (1 / 2 : ℂ) * (q : ℂ) ^ (-star c.value) := by
  unfold Kernel.A
  linear_combination -GapEuler.gapMean_primitive q (by norm_num) c

/-- The full original base is generated from the same radial source, including its A contact. -/
theorem original_base_step_reconstruction (c : BurnolCompletedMellinCoordinate) :
    KCountingSource.base c = Kernel.A c • ConstantDual.seed - returnStepIntegral c +
      (star c.value / 2) • tailStepIntegral c := by
  have cNonzero : star c.value ≠ 0 := by
    intro zero
    have realPart := congrArg Complex.re zero
    simp only [star_def, conj_re, zero_re] at realPart
    linarith [c.rightHalf]
  apply Lp.ext
  filter_upwards [KCountingSource.base_coeFn c,
    Lp.coeFn_add (Kernel.A c • ConstantDual.seed - returnStepIntegral c)
      ((star c.value / 2) • tailStepIntegral c),
    Lp.coeFn_sub (Kernel.A c • ConstantDual.seed) (returnStepIntegral c),
    Lp.coeFn_smul (Kernel.A c) ConstantDual.seed,
    Lp.coeFn_smul (star c.value / 2) (tailStepIntegral c), ConstantDual.seed_coeFn,
    returnStepIntegral_coeFn c, tailStepIntegral_coeFn c, volume.ae_ne (0 : ℝ)]
      with x base addition difference scalar scalarTail step returned tail nonzero
  rw [base, addition, Pi.add_apply, difference, Pi.sub_apply, scalar, Pi.smul_apply,
    smul_eq_mul, scalarTail, Pi.smul_apply, smul_eq_mul, step, returned, tail]
  by_cases inside : |x| ≤ q
  · have primitive : (∫ t : ℝ in Ioc |x| q, burnolRieszReturnRawDerivative c t) =
        burnolRieszReturnRaw c q - burnolRieszReturnRaw c |x| := by
      rw [← intervalIntegral.integral_of_le inside]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => burnolRieszReturnRaw_hasDerivAt c t)
        ((burnolRieszReturnRawDerivative_continuous c).intervalIntegrable _ _)
    rw [KCountingSource.baseRaw, if_pos inside, ConstantDual.seedRaw, if_pos inside,
      max_eq_left inside, primitive, A_original_gap]
    field_simp
    ring
  · have empty : Ioc |x| q = ∅ := Ioc_eq_empty_of_le (le_of_not_ge inside)
    rw [KCountingSource.baseRaw, if_neg inside, ConstantDual.seedRaw, if_neg inside,
      mul_zero, empty, max_eq_right (le_of_not_ge inside)]
    simp only [setIntegral_empty, sub_zero, zero_add]
    field_simp

end
end OriginalGamma.Source.CountingQuadratic
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
