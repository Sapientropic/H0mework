import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaRadialRawSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaQuarterGapHeatSource
import H0mework.Arithmetic.BurnolCarrier.AdditiveL2
import H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.QuarterMellinAdditiveEvenRechart

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.WeightedRadialKernel

open MeasureTheory Set Filter
open OriginalGamma.Source.CountingQuadraticLimit OriginalGamma.Source.FiniteLogCounting
open OriginalGamma.Source.RelativeConductorGapReadback

open private integrableOn_exp_weight_iff from
  H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.QuarterMellinAdditiveEvenRechart
open private integral_exp_weight from
  H0mework.Arithmetic.BurnolCarrier.AdditiveL2
open private tail_weight_memLp from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaQuarterGapHeatSource
open private radial_synthesis_raw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaRadialRawSource
open private gamma_pair_synthesis from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback

def IntegrableKernel (source : ℝ → ℂ) : Prop :=
  IntegrableOn (fun x : ℝ => (Real.sqrt x)⁻¹ * ‖source x‖) (Ioi 0)

private def logWeight (x : ℝ) : ℝ := (Real.sqrt x * (1 + |Real.log x|))⁻¹

private theorem log_weight_memLp : MemLp logWeight 2 (volume.restrict (Ioi 0)) := by
  have measured : Measurable logWeight := by unfold logWeight; fun_prop
  rw [memLp_two_iff_integrable_sq_norm measured.aestronglyMeasurable]
  apply (integrableOn_exp_weight_iff _).mpr
  have source := (memLp_two_iff_integrable_sq_norm tail_weight_memLp.1).mp tail_weight_memLp
  apply source.congr
  filter_upwards with t
  change ‖(1 + |t|)⁻¹‖ ^ 2 = Real.exp t * ‖logWeight (Real.exp t)‖ ^ 2
  have q : 0 < Real.sqrt (Real.exp t) := Real.sqrt_pos.mpr (Real.exp_pos t)
  have h : 0 < 1 + |t| := by positivity
  rw [logWeight, Real.log_exp, Real.norm_of_nonneg (inv_nonneg.mpr h.le),
    Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg q.le h.le)), mul_inv_rev, mul_pow]
  simp only [inv_pow, Real.sq_sqrt (Real.exp_pos t).le]
  field_simp [Real.exp_ne_zero t]

/-- A paid position log gives the absolute mass of the original dilation kernel. -/
theorem kernel_of_log (value logged : BurnolL2) (source : LogPair value logged) :
    IntegrableKernel value := by
  have both : MemLp (fun x : ℝ => ‖value x‖ + ‖logged x‖) 2 (volume.restrict (Ioi 0)) :=
    ((Lp.memLp value).norm.add (Lp.memLp logged).norm).mono_measure Measure.restrict_le_self
  apply (log_weight_memLp.integrable_mul both).congr
  filter_upwards [ae_restrict_of_ae (s := Ioi (0 : ℝ)) source, ae_restrict_mem measurableSet_Ioi]
    with x read positive
  change logWeight x * (‖value x‖ + ‖logged x‖) = (Real.sqrt x)⁻¹ * ‖value x‖
  have pos : 0 < x := positive
  rw [read, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pos, logWeight, mul_inv_rev]
  have joined : ‖value x‖ + |Real.log x| * ‖value x‖ = (1+|Real.log x|) * ‖value x‖ := by ring
  have nonzero : 1+|Real.log x| ≠ 0 := by positivity
  rw [joined]
  field_simp [nonzero, (Real.sqrt_pos.mpr pos).ne']

def coefficient (source : ℝ → ℂ) (t : ℝ) : ℂ := source (4*t) / (t : ℂ)

private theorem coefficient_measurable (source : ℝ → ℂ) (measured : Measurable source) :
    Measurable (coefficient source) := (measured.comp (by fun_prop)).div Complex.measurable_ofReal

private theorem coefficient_weighted (source : ℝ → ℂ) (mass : IntegrableKernel source) :
    IntegrableOn (fun t => Real.sqrt t * ‖coefficient source t‖) (Ioi 0) := by
  have scaled := (integrableOn_Ioi_comp_mul_left_iff (fun x => (Real.sqrt x)⁻¹ * ‖source x‖)
    0 (a := 4) (by norm_num)).mpr (by simpa only [mul_zero, IntegrableKernel] using mass)
  apply (scaled.const_mul 2).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have pos : 0 < t := ht
  have root : Real.sqrt (4*t) = 2*Real.sqrt t := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  have ratio : Real.sqrt t / t = (Real.sqrt t)⁻¹ := by
    calc
      _ = Real.sqrt t / (Real.sqrt t)^2 := by rw [Real.sq_sqrt pos.le]
      _ = _ := by field_simp [(Real.sqrt_pos.mpr pos).ne']
  change 2 * ((Real.sqrt (4*t))⁻¹ * ‖source (4*t)‖) = _
  rw [coefficient, norm_div, Complex.norm_real, Real.norm_of_nonneg pos.le, root, mul_inv_rev]
  calc
    _ = (Real.sqrt t)⁻¹ * ‖source (4*t)‖ := by ring
    _ = Real.sqrt t * (‖source (4*t)‖ / t) := by rw [← ratio]; ring

/-- The existing radial synthesis with the actual source profile and its absolute mass. -/
def action (source : ℝ → ℂ) (measured : Measurable source) (mass : IntegrableKernel source) :
    BurnolL2 →L[ℂ] BurnolL2 :=
  radialSynthesisCLM (Ioi 0) measurableSet_Ioi Subset.rfl (coefficient source)
    (coefficient_measurable source measured) (coefficient_weighted source mass)

theorem action_value (source : ℝ → ℂ) (measured : Measurable source) (mass : IntegrableKernel source)
    (value : BurnolL2) :
    action source measured mass value = ∫ t in Ioi 0, coefficient source t • radialOrbit t value := rfl

theorem action_gamma (source : ℝ → ℂ) (measured : Measurable source) (mass : IntegrableKernel source)
    (v gamma : BurnolL2) (graph : GammaPair v gamma) :
    GammaPair (action source measured mass v) (action source measured mass gamma) :=
  gamma_pair_synthesis _ measurableSet_Ioi Subset.rfl _ (coefficient_measurable source measured)
    (coefficient_weighted source mass) _ _ graph

private theorem action_raw (source : ℝ → ℂ) (measured : Measurable source) (mass : IntegrableKernel source)
    (v : BurnolL2) (raw : ℝ → ℂ) (rawMeasured : Measurable raw) (read : (v : ℝ → ℂ) =ᵐ[volume] raw) :
    (action source measured mass v : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ t in Ioi 0, coefficient source t * raw (x/(4*t)) :=
  radial_synthesis_raw _ measurableSet_Ioi Subset.rfl _ (coefficient_measurable source measured)
    (coefficient_weighted source mass) _ _ rawMeasured read

private theorem integral_log (u v : ℝ → ℂ) (x : ℝ) :
    (∫ t in Ioi 0, coefficient u t * v (x/(4*t))) =
      ∫ t : ℝ, u (4*Real.exp t) * v (x/(4*Real.exp t)) := by
  rw [← integral_exp_weight]
  apply integral_congr_ae
  filter_upwards with t
  change (Real.exp t : ℂ) * (u (4*Real.exp t) / (Real.exp t : ℂ) *
      v (x/(4*Real.exp t))) = _
  field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)]

private theorem integral_swap (u v : ℝ → ℂ) (x : ℝ) (positive : 0 < x) :
    (∫ t in Ioi 0, coefficient u t * v (x/(4*t))) =
      ∫ t in Ioi 0, coefficient v t * u (x/(4*t)) := by
  rw [integral_log, integral_log]
  let other (t : ℝ) := v (4*Real.exp t) * u (x/(4*Real.exp t))
  have clock : 0 < x/16 := by positivity
  calc
    _ = ∫ t : ℝ, other (Real.log (x/16)-t) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [other]
      rw [Real.exp_sub, Real.exp_log clock,
        show 4*(x/16 / Real.exp t) = x/(4*Real.exp t) by field_simp; ring,
        show x/(x/(4*Real.exp t)) = 4*Real.exp t by
          field_simp [positive.ne', Real.exp_ne_zero t]]
      exact mul_comm _ _
    _ = ∫ t : ℝ, other (Real.log (x/16)+t) := by
      simpa only [sub_eq_add_neg] using integral_neg_eq_self (fun t => other (Real.log (x/16)+t)) volume
    _ = ∫ t : ℝ, other t :=
      integral_add_left_eq_self (μ := (volume : Measure ℝ)) other (Real.log (x/16))

private theorem integral_abs (u v : ℝ → ℂ) (even : ∀ x, v (-x) = v x) (x : ℝ) :
    (∫ t in Ioi 0, coefficient u t * v (x/(4*t))) =
      ∫ t in Ioi 0, coefficient u t * v (|x|/(4*t)) := by
  apply integral_congr_ae
  filter_upwards with t
  rcases le_or_gt 0 x with pos | neg
  · rw [abs_of_nonneg pos]
  · rw [abs_of_neg neg, neg_div, even]

/-- The two actual even dilation kernels commute on their original fields. -/
theorem action_swap (u v : BurnolL2) (ur vr : ℝ → ℂ)
    (um : Measurable ur) (vm : Measurable vr) (ui : IntegrableKernel ur) (vi : IntegrableKernel vr)
    (uRead : (u : ℝ → ℂ) =ᵐ[volume] ur) (vRead : (v : ℝ → ℂ) =ᵐ[volume] vr)
    (ue : ∀ x, ur (-x) = ur x) (ve : ∀ x, vr (-x) = vr x) :
    action ur um ui v = action vr vm vi u := by
  apply Lp.ext
  filter_upwards [action_raw ur um ui v vr vm vRead, action_raw vr vm vi u ur um uRead,
    volume.ae_ne (0 : ℝ)] with x left right nonzero
  rw [left, right, integral_abs ur vr ve, integral_abs vr ur ue]
  exact integral_swap ur vr |x| (abs_pos.mpr nonzero)

end OriginalGamma.Source.WeightedRadialKernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
