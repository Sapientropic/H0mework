import H0mework.Arithmetic.Muntz.CoPoissonSchwartzEnergyAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorStrongSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier
import H0mework.Versions.R7e4da746.Arithmetic.SonineProjection.ConstructorCompact
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Trace
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.SourceDerivative
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.RawDerivative
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.RelativeConductorGapReadback
open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.JointLogConductor
open OriginalGamma.Source.CountingQuadraticLimit OriginalGamma.Source.CountingQuadratic
open OriginalGamma.Source.DivisorJoint OriginalGamma.Source.RelativeConductorStrong
noncomputable section
local notation "q" => (1 / 4 : ℝ)
private theorem reflected_inverse_log (test : SchwartzMap ℝ ℂ) :
    reflectL2 (logSchwartzL2 (𝓕⁻ test)) = logSchwartzL2 (𝓕 test) := by
  apply Lp.ext
  have inverseRaw := negMeasurePreserving.quasiMeasurePreserving.ae (original_log_schwartz_raw (𝓕⁻ test))
  filter_upwards [Lp.coeFn_compMeasurePreserving (logSchwartzL2 (𝓕⁻ test)) negMeasurePreserving,
    inverseRaw, original_log_schwartz_raw (𝓕 test)] with x reflected inverse forward
  change reflectL2 (logSchwartzL2 (𝓕⁻ test)) x = logSchwartzL2 (𝓕⁻ test) (-x) at reflected
  rw [reflected, inverse, forward, abs_neg]
  congr 1
  rw [SchwartzMap.fourierInv_apply_eq]
  change (𝓕 test) (-(-x)) = (𝓕 test) x
  rw [neg_neg]

theorem original_whole_Gamma_fourier_source (test : SchwartzMap ℝ ℂ) :
    wholeConductorTest (𝓕 test) = fourierL2 (wholeConductorTest test) := by
  unfold wholeConductorTest
  rw [FourierTransform.fourierInv_fourier_eq, map_add, fourierL2_fourierL2,
    reflected_inverse_log]
  exact add_comm _ _



def GammaPair (v gamma : BurnolL2) : Prop :=
  ∀ test : SchwartzMap ℝ ℂ, inner ℂ (wholeConductorTest test) v = inner ℂ (test.toLp 2 volume) gamma

private theorem log_pair_dilation (h : ℝ) (v logv : BurnolL2) (source : LogPair v logv) :
    LogPair (burnolMultiplicativeDilation h v)
      (burnolMultiplicativeDilation h logv - (h : ℂ) • burnolMultiplicativeDilation h v) := by
  have moved := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (Real.exp_ne_zero h)).ae source
  filter_upwards [Lp.coeFn_sub (burnolMultiplicativeDilation h logv)
      ((h : ℂ) • burnolMultiplicativeDilation h v),
    Lp.coeFn_smul (h : ℂ) (burnolMultiplicativeDilation h v),
    burnolMultiplicativeDilation_coeFn h logv, burnolMultiplicativeDilation_coeFn h v,
    moved, volume.ae_ne (0 : ℝ)] with x subtraction scalar left right actual nonzero
  rw [subtraction]
  change burnolMultiplicativeDilation h logv x - ((h : ℂ) • burnolMultiplicativeDilation h v) x = _
  rw [scalar, Pi.smul_apply, smul_eq_mul, left, right]
  unfold burnolL2RawNormalizedDilation
  change logv (Real.exp h * x) = (Real.log |Real.exp h * x| : ℂ) * v (Real.exp h * x) at actual
  rw [actual]
  have logarithm : Real.log |Real.exp h * x| = h + Real.log |x| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos h),
      Real.log_mul (Real.exp_ne_zero h) (abs_ne_zero.mpr nonzero), Real.log_exp]
  rw [logarithm]
  push_cast
  ring

private theorem log_pair_unique (v l r : BurnolL2) (hl : LogPair v l) (hr : LogPair v r) : l = r := by
  exact Lp.ext (hl.trans hr.symm)

private theorem log_schwartz_dilation (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    logSchwartzL2 (coPoissonSchwartzEnergyTranslationEquiv h test) =
      burnolMultiplicativeDilation h (logSchwartzL2 test) -
        (h : ℂ) • burnolMultiplicativeDilation h (test.toLp 2 volume) := by
  have source := log_pair_dilation h _ _ (original_log_schwartz_domain test)
  rw [burnolMultiplicativeDilation_schwartz] at source
  have read := log_pair_unique _ _ _ (original_log_schwartz_domain _) source
  rw [← burnolMultiplicativeDilation_schwartz] at read
  exact read

private theorem inverse_fourier_dilation (h : ℝ) (v : BurnolL2) :
    fourierL2.symm (burnolMultiplicativeDilation h v) =
      burnolMultiplicativeDilation (-h) (fourierL2.symm v) := by
  apply fourierL2.injective
  rw [fourierL2.apply_symm_apply, fourierL2_burnolMultiplicativeDilation,
    neg_neg, fourierL2.apply_symm_apply]

private theorem inverse_log_schwartz_dilation (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    logSchwartzL2 (𝓕⁻ (coPoissonSchwartzEnergyTranslationEquiv h test)) =
      burnolMultiplicativeDilation (-h) (logSchwartzL2 (𝓕⁻ test)) +
        (h : ℂ) • burnolMultiplicativeDilation (-h) ((𝓕⁻ test).toLp 2 volume) := by
  have source := log_pair_dilation (-h) _ _ (original_log_schwartz_domain (𝓕⁻ test))
  have same : (𝓕⁻ (coPoissonSchwartzEnergyTranslationEquiv h test)).toLp 2 volume =
      burnolMultiplicativeDilation (-h) ((𝓕⁻ test).toLp 2 volume) := by
    rw [← SchwartzMap.toLp_fourierInv_eq, ← burnolMultiplicativeDilation_schwartz,
      ← SchwartzMap.toLp_fourierInv_eq]
    exact inverse_fourier_dilation h (test.toLp 2 volume)
  rw [← same] at source
  have read := log_pair_unique _ _ _ (original_log_schwartz_domain _) source
  rw [same] at read
  simpa only [ofReal_neg, neg_smul, sub_neg_eq_add] using read

/-- Both actual logarithm shifts cancel in the complete conductor. -/
theorem original_whole_Gamma_dilation_source (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    wholeConductorTest (coPoissonSchwartzEnergyTranslationEquiv h test) =
      burnolMultiplicativeDilation h (wholeConductorTest test) := by
  unfold wholeConductorTest
  rw [log_schwartz_dilation, inverse_log_schwartz_dilation, map_add, map_smul,
    fourierL2_burnolMultiplicativeDilation, neg_neg,
    fourierL2_burnolMultiplicativeDilation, neg_neg]
  have inverse : fourierL2 ((𝓕⁻ test).toLp 2 volume) = test.toLp 2 volume := by
    change 𝓕 ((𝓕⁻ test).toLp 2 volume) = test.toLp 2 volume
    rw [SchwartzMap.toLp_fourier_eq, FourierTransform.fourier_fourierInv_eq]
  rw [inverse, map_add]
  module

private theorem dilation_pair (h : ℝ) (left right : BurnolL2) :
    inner ℂ left (burnolMultiplicativeDilation h right) =
      inner ℂ (burnolMultiplicativeDilation (-h) left) right := by
  have source := (burnolMultiplicativeDilation h).inner_map_map
    ((burnolMultiplicativeDilation h).symm left) right
  simp only [LinearIsometryEquiv.apply_symm_apply] at source
  rw [← burnolMultiplicativeDilation_neg_eq_symm] at source
  exact source

private theorem gamma_pair_dilation (h : ℝ) (v gamma : BurnolL2) (source : GammaPair v gamma) :
    GammaPair (burnolMultiplicativeDilation h v) (burnolMultiplicativeDilation h gamma) := by
  intro test
  rw [dilation_pair, ← original_whole_Gamma_dilation_source,
    source, ← burnolMultiplicativeDilation_schwartz]
  exact (dilation_pair h (test.toLp 2 volume) gamma).symm

private theorem gamma_pair_radial (t : ℝ) (v gamma : BurnolL2) (source : GammaPair v gamma) :
    GammaPair (radialOrbit t v) (radialOrbit t gamma) := by
  intro test
  unfold radialOrbit
  rw [inner_smul_right, inner_smul_right]
  exact congrArg (fun z : ℂ => (Real.exp (Real.log (4 * t) / 2) : ℂ) * z)
    (gamma_pair_dilation _ v gamma source test)

private theorem radial_integrable (s : Set ℝ) (hs : MeasurableSet s) (positive : s ⊆ Ioi 0)
    (coefficient : ℝ → ℂ) (measured : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖coefficient t‖) s) (v : BurnolL2) :
    IntegrableOn (fun t => coefficient t • radialOrbit t v) s := by
  have regular : AEStronglyMeasurable (fun t => coefficient t • radialOrbit t v) (volume.restrict s) :=
    measured.aestronglyMeasurable.smul
    (((radialOrbit_continuous v).mono positive).aestronglyMeasurable hs)
  apply (integrable_norm_iff regular).mp
  apply (weighted.const_mul (2 * ‖v‖)).congr
  filter_upwards [ae_restrict_mem hs] with t inside
  rw [norm_smul, radialOrbit_norm t (positive inside) v]
  ring

private theorem gamma_pair_synthesis (s : Set ℝ) (hs : MeasurableSet s) (positive : s ⊆ Ioi 0)
    (coefficient : ℝ → ℂ) (measured : Measurable coefficient)
    (weighted : IntegrableOn (fun t : ℝ => Real.sqrt t * ‖coefficient t‖) s)
    (v gamma : BurnolL2) (source : GammaPair v gamma) :
    GammaPair (radialSynthesisCLM s hs positive coefficient measured weighted v)
      (radialSynthesisCLM s hs positive coefficient measured weighted gamma) := by
  intro test
  rw [radialSynthesisCLM_apply, radialSynthesisCLM_apply]
  have left := (innerSL ℂ (wholeConductorTest test)).integral_comp_comm
    (radial_integrable s hs positive coefficient measured weighted v)
  have right := (innerSL ℂ (test.toLp 2 volume)).integral_comp_comm
    (radial_integrable s hs positive coefficient measured weighted gamma)
  simp only [innerSL_apply_apply] at left right
  rw [← left, ← right]
  apply integral_congr_ae
  filter_upwards with t
  change inner ℂ (wholeConductorTest test) (coefficient t • radialOrbit t v) =
    inner ℂ (test.toLp 2 volume) (coefficient t • radialOrbit t gamma)
  rw [inner_smul_right, inner_smul_right, gamma_pair_radial t v gamma source test]

private theorem gamma_pair_inverse_fourier (v gamma : BurnolL2) (source : GammaPair v gamma) :
    GammaPair (fourierL2.symm v) (fourierL2.symm gamma) := by
  intro test
  calc
    _ = inner ℂ (fourierL2 (wholeConductorTest test)) v := by
      rw [fourierL2.inner_map_eq_flip]
    _ = inner ℂ (wholeConductorTest (𝓕 test)) v := by rw [original_whole_Gamma_fourier_source]
    _ = inner ℂ ((𝓕 test).toLp 2 volume) gamma := source (𝓕 test)
    _ = inner ℂ (test.toLp 2 volume) (fourierL2.symm gamma) := by
      rw [← SchwartzMap.toLp_fourier_eq]
      exact fourierL2.inner_map_eq_flip _ _

private theorem gamma_pair_base (c : BurnolCompletedMellinCoordinate) (v gamma : BurnolL2)
    (source : GammaPair v gamma) :
    GammaPair (originalBaseSynthesis c v) (originalBaseSynthesis c gamma) := by
  have returned : GammaPair (returnSynthesis c v) (returnSynthesis c gamma) :=
    gamma_pair_synthesis (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
      (burnolRieszReturnRawDerivative c) (burnolRieszReturnRawDerivative_continuous c).measurable
      (return_weighted_integrable c) v gamma source
  have tail : GammaPair (tailSynthesis c v) (tailSynthesis c gamma) :=
    gamma_pair_synthesis (Ioi q) measurableSet_Ioi (Ioi_subset_Ioi (by norm_num))
      (fun t : ℝ => (t : ℂ) ^ (-star c.value - 1)) (whole_tail_measurable c)
      (tail_weighted_integrable c) v gamma source
  intro test
  simp only [originalBaseSynthesis, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, inner_sub_right, inner_smul_right]
  rw [source test, returned test, tail test]

private theorem gamma_pair_b (c : BurnolCompletedMellinCoordinate) (v gamma : BurnolL2)
    (source : GammaPair v gamma) :
    GammaPair (originalBSynthesis c v) (originalBSynthesis c gamma) := by
  have original : GammaPair (bSynthesis c v) (bSynthesis c gamma) :=
    gamma_pair_synthesis (Ioc 0 q) measurableSet_Ioc Ioc_subset_Ioi_self
      (sourceRawDerivative c) (source_slope_measurable c) (b_weighted_slope_integrable c) v gamma source
  intro test
  simp only [originalBSynthesis, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_sub_right, inner_smul_right]
  rw [source test, original test]

end
end OriginalGamma.Source.RelativeConductorGapReadback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
