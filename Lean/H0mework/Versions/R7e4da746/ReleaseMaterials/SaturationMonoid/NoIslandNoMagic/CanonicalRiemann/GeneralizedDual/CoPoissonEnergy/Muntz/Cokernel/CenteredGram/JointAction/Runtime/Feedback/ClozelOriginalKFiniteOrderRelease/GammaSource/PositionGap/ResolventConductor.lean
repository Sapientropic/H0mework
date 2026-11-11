import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorWindowFactor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Physical
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.LogAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.WeightedRadialKernel

open MeasureTheory Set Filter
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.JointLogConductor
open OriginalGamma.Source.KGamma OriginalGamma.Source.KGamma.Iterated OriginalGamma.Source.GammaRadialRaw
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.ConductorDual
open CenteredGram.IntegralGraphJointAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open OriginalRSourceJointContact.LogAction
open scoped InnerProductSpace

open private even_position_log_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WindowLog.Physical
open private gamma_pair_dilation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private inverse_log_from_complete_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource

local notation "q" => (1/4 : ℝ)
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "Ev" => burnolAmbientEvenPart

private theorem gamma_window_mass : IntegrableKernel gammaSeedRaw := by
  apply (kernel_of_log _ _ actual_gamma_seed_position_log).congr
  filter_upwards [ae_restrict_of_ae (s := Ioi (0:ℝ)) actual_gamma_seed_whole_raw] with x read
  rw [read]

private def gammaWindow : BurnolL2 →L[ℂ] BurnolL2 :=
  action gammaSeedRaw gammaSeedRaw_measurable gamma_window_mass

private def evenRaw (v : BurnolL2) (x : ℝ) : ℂ := v |x|

private theorem even_raw_read (v : BurnolL2) (even : reflectL2 v = v) :
    (v : ℝ → ℂ) =ᵐ[volume] evenRaw v := by
  have reflectRead := Lp.coeFn_compMeasurePreserving v negMeasurePreserving
  change (reflectL2 v : ℝ → ℂ) =ᵐ[volume] fun x => v (-x) at reflectRead
  rw [even] at reflectRead
  filter_upwards [reflectRead] with x read
  rcases le_or_gt 0 x with positive | negative
  · rw [evenRaw, abs_of_nonneg positive]
  · rw [evenRaw, abs_of_neg negative]
    exact read

private theorem gamma_window_of_log (v logged : BurnolL2) (even : reflectL2 v = v)
    (log : LogPair v logged) : GammaPair (windowKernel v) (gammaWindow v) := by
  have measured : Measurable (evenRaw v) := (Lp.stronglyMeasurable v).measurable.comp (by fun_prop : Measurable (fun x : ℝ => |x|))
  have read := even_raw_read v even
  have mass : IntegrableKernel (evenRaw v) := by
    apply (kernel_of_log v logged log).congr
    filter_upwards [ae_restrict_of_ae (s := Ioi (0:ℝ)) read] with x same
    rw [same]
  have ve (x : ℝ) : evenRaw v (-x) = evenRaw v x := by rw [evenRaw, evenRaw, abs_neg]
  have ce (x : ℝ) : ConstantDual.seedRaw (-x) = ConstantDual.seedRaw x := by
    rw [ConstantDual.seedRaw, ConstantDual.seedRaw, abs_neg]
  have input := action_swap ConstantDual.seed v ConstantDual.seedRaw (evenRaw v)
    ConstantDual.seedRaw_measurable measured window_mass mass ConstantDual.seed_coeFn read ce ve
  have acted := action_swap actualGammaSeed v gammaSeedRaw (evenRaw v) gammaSeedRaw_measurable
    measured gamma_window_mass mass actual_gamma_seed_whole_raw read gammaSeedRaw_even ve
  unfold windowKernel gammaWindow
  rw [input, acted]
  exact action_gamma _ _ _ _ _ actual_gamma_seed_source

private theorem even_dense_induction (v : BurnolL2) (even : reflectL2 v = v)
    {p : BurnolL2 → Prop} (closed : IsClosed {w | p w})
    (tests : ∀ test : SchwartzMap ℝ ℂ, p (Ev (test.toLp 2 volume))) : p v := by
  have cont : Continuous Ev :=
    (continuous_id.add reflectL2.continuous).const_smul (1/2 : ℂ)
  have dense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  have observed := dense.induction_on (p := fun w : BurnolL2 => p (Ev w)) v
    (closed.preimage cont) tests
  have fixed : Ev v = v := by
    rw [burnolAmbientEvenPart, even, ← two_smul ℂ v, smul_smul]
    norm_num
  rwa [fixed] at observed

private theorem window_gamma (v : BurnolL2) (even : reflectL2 v = v) :
    GammaPair (windowKernel v) (gammaWindow v) := by
  intro test
  apply even_dense_induction v even
    (p := fun w => inner ℂ (wholeConductorTest test) (windowKernel w) =
      inner ℂ (test.toLp 2 volume) (gammaWindow w))
  · exact isClosed_eq (continuous_const.inner windowKernel.continuous)
      (continuous_const.inner gammaWindow.continuous)
  · intro probe
    exact gamma_window_of_log _ _ (burnolAmbientEvenPart_even _)
      (even_position_log_pair _ _ (original_log_schwartz_domain probe)) test

private def normalizedGammaWindow : BurnolL2 →L[ℂ] BurnolL2 :=
  (-4 : ℂ) • (D (Real.log q)).toContinuousLinearEquiv.toContinuousLinearMap.comp gammaWindow

private theorem outward_gamma (v : BurnolL2) (even : reflectL2 v = v) :
    GammaPair (F (burnolDirectRightResolvent (1/2) (fourierL2.symm v))) (normalizedGammaWindow v) := by
  have paid := gamma_pair_dilation (Real.log q) _ _ (window_gamma v even)
  rw [← window_factor]
  intro test
  change inner ℂ (wholeConductorTest test) ((-4 : ℂ) • D (Real.log q) (windowKernel v)) =
    inner ℂ (test.toLp 2 volume) ((-4 : ℂ) • D (Real.log q) (gammaWindow v))
  rw [inner_smul_right, inner_smul_right, paid test]

private theorem right_quarter (c : BurnolCompletedMellinCoordinate) : 1/4 < (c.value/2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [c.rightHalf]

/-- The original window conductor kernel followed by the actual mixed-resolvent factor. -/
def gammaR (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  -(normalizedGammaWindow + (c.value/2) • (R c).comp normalizedGammaWindow)

theorem actual_gamma_R (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) : GammaPair (R c v) (gammaR c v) := by
  let out := F (burnolDirectRightResolvent (1/2) (fourierL2.symm v))
  have mixed := burnolDirectRightResolvent_fourier_mixed (c.value/2) (1/2)
    (right_quarter c) (by norm_num) (fourierL2.symm v)
  rw [fourierL2.apply_symm_apply, show c.value/2 + 1/2 - 1/2 = c.value/2 by ring] at mixed
  change (c.value/2) • R c out = -(R c v + out) at mixed
  have source : R c v = -(out + (c.value/2) • R c out) := by
    linear_combination (norm := module) mixed
  have outward : GammaPair out (normalizedGammaWindow v) := outward_gamma v even
  have acted : GammaPair (R c out) (R c (normalizedGammaWindow v)) :=
    actual_Gamma_R c out _ outward
  rw [source]
  intro test
  change inner ℂ (wholeConductorTest test) (-(out + (c.value/2) • R c out)) =
    inner ℂ (test.toLp 2 volume) (-(normalizedGammaWindow v + (c.value/2) • R c (normalizedGammaWindow v)))
  simp only [inner_neg_right, inner_add_right, inner_smul_right, outward test, acted test]

/-- The bounded composed action pays its exact dual price against any original strong log field. -/
theorem actual_gamma_R_dual (c : BurnolCompletedMellinCoordinate) (v u gamma position inverse : BurnolL2)
    (even : reflectL2 v = v) (graph : GammaPair u gamma)
    (hp : LogPair u position) (hf : LogPair (fourierL2.symm u) inverse) :
    inner ℂ gamma (R c v) = inner ℂ u (gammaR c v) := by
  apply even_dense_induction v even
    (p := fun w => inner ℂ gamma (R c w) = inner ℂ u (gammaR c w))
  · exact isClosed_eq (continuous_const.inner (R c).continuous)
      (continuous_const.inner (gammaR c).continuous)
  · intro test
    let actual := Ev (test.toLp 2 volume)
    have inputLog := even_position_log_pair _ _ (original_log_schwartz_domain test)
    have outputLog := actual_direct_R_log (c.value/2) (right_quarter c) _ _ inputLog
    have source := actual_gamma_R c actual (burnolAmbientEvenPart_even _)
    have inverseLog := inverse_log_from_complete_source _ _ _ source outputLog
    exact whole_conductor_dual _ _ _ _ _ _ _ _ graph source hp hf outputLog inverseLog

end OriginalGamma.Source.WeightedRadialKernel
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
