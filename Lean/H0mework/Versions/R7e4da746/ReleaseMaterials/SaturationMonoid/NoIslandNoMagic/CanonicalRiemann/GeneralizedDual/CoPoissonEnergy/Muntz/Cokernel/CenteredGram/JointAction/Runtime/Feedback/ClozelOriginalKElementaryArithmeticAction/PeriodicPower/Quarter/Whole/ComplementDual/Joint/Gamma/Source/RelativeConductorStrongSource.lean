import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.DivisorJointSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.LogPairClosureSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SmallScaleLog
import H0mework.Arithmetic.TruncatedFourier.ActualBridge
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.RelativeConductorStrong
open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.CountingQuadraticLimit OriginalGamma.Source.CountingQuadratic
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.DivisorJoint
noncomputable section
local notation "q" => (1 / 4 : ℝ)
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



def logSeedSynthesis : BurnolL2 →L[ℂ] BurnolL2 :=
  (Real.log q : ℂ) • ContinuousLinearMap.id ℂ BurnolL2 - logSynthesis

private theorem log_seed_synthesis_apply (v : BurnolL2) :
    logSeedSynthesis v = (Real.log q : ℂ) • v - logSynthesis v := by
  simp only [logSeedSynthesis, sub_apply, smul_apply, ContinuousLinearMap.id_apply]

private theorem log_seed_source : compactLog = logSeedSynthesis ConstantDual.seed := by
  rw [log_seed_synthesis_apply]
  exact compact_log_reconstruct

private theorem log_seed_synthesis_joint (v : BurnolL2) :
    logSeedSynthesis (joint v) = joint (logSeedSynthesis v) := by
  rw [log_seed_synthesis_apply, log_seed_synthesis_apply, map_sub, map_smul]
  congr 1
  exact (radial_commute joint joint_dilation (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
    (fun t : ℝ => (t : ℂ)⁻¹) (by fun_prop) inv_weighted v).symm

private theorem log_pair_pairing (left logLeft right logRight : BurnolL2)
    (hl : LogPair left logLeft) (hr : LogPair right logRight) :
    inner ℂ logLeft right = inner ℂ left logRight := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hl, hr] with x first second
  rw [first, second]
  rw [RCLike.inner_apply, RCLike.inner_apply]
  change right x * star (↑(Real.log |x|) * left x) = (↑(Real.log |x|) * right x) * star (left x)
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

end
end OriginalGamma.Source.RelativeConductorStrong
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
