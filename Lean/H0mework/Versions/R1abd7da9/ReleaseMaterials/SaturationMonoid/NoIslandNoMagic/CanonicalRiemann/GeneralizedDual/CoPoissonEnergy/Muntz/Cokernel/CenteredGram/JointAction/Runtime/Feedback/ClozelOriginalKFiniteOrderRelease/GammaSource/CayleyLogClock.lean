import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.CayleyLogClock.PositiveTimeTriangle
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.LogAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.CayleyLogClock

open Complex Filter MeasureTheory Set
open CenteredGram.IntegralGraphJointAction
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.ConductorDual OriginalGamma.Source.JointLogConductor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalRSourceJointContact.LogAction
open scoped InnerProductSpace

open private log_pair_add from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
open private logPair_smul from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource
open private inverse_log_from_complete_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource

local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioi (0 : ℝ))
local notation "R" => burnolDirectRightResolventCLM
local notation "C" => sourceCayley
local notation "δ" => sourceDamping
local notation "F" => fourierL2

private theorem integrand_add (z : ℂ) (v : BurnolL2) (s t : ℝ) :
    burnolDirectRightResolventIntegrand z v (s + t) =
      positiveMellinQuarterRightResolventWeight z s • burnolMultiplicativeDilation (-s / 2)
        (burnolDirectRightResolventIntegrand z v t) := by
  unfold burnolDirectRightResolventIntegrand
  rw [positiveMellinQuarterRightResolventWeight_add, map_smul, smul_smul,
    burnolMultiplicativeDilation_add, show -s / 2 + -t / 2 = -(s + t) / 2 by ring]

private theorem integrand_square_integrable (z : ℂ) (right : 1 / 4 < z.re) (v : BurnolL2) :
    Integrable (fun p : ℝ × ℝ => burnolDirectRightResolventIntegrand z v (p.1 + p.2))
      (Measure.prod μ₊ μ₊) := by
  have weight : Integrable (positiveMellinQuarterRightResolventWeight z) μ₊ := by
    apply (exp_neg_integrableOn_Ioi 0 (sub_pos.mpr right)).mono'
      (positiveMellinQuarterRightResolventWeight_continuous z).aestronglyMeasurable
    exact Eventually.of_forall fun t => (norm_positiveMellinQuarterRightResolventWeight z t).le
  have envelope := weight.smul_prod (burnolDirectRightResolventIntegrand_integrableOn z right v)
  have continuous : Continuous (burnolDirectRightResolventIntegrand z v) :=
    (positiveMellinQuarterRightResolventWeight_continuous z).smul
      ((burnolMultiplicativeDilation_stronglyContinuous v).comp (by fun_prop))
  apply envelope.norm.mono' (continuous.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖burnolDirectRightResolventIntegrand z v (p.1 + p.2)‖ ≤
      ‖positiveMellinQuarterRightResolventWeight z p.1 • burnolDirectRightResolventIntegrand z v p.2‖
    rw [integrand_add, norm_smul, (burnolMultiplicativeDilation (-p.1 / 2)).norm_map, norm_smul]

private theorem square_integral (z : ℂ) (right : 1 / 4 < z.re) (v : BurnolL2) :
    burnolDirectRightResolvent z (burnolDirectRightResolvent z v) =
      ∫ r in Ioi (0 : ℝ), r • burnolDirectRightResolventIntegrand z v r := by
  let f := burnolDirectRightResolventIntegrand z v
  have acted (s : ℝ) : burnolDirectRightResolventIntegrand z (burnolDirectRightResolvent z v) s =
      -(∫ t in Ioi (0 : ℝ), f (s + t)) := by
    let D := (burnolMultiplicativeDilation (-s / 2)).toLinearIsometry
    change positiveMellinQuarterRightResolventWeight z s • D (-(∫ t in Ioi (0 : ℝ), f t)) = _
    rw [map_neg, smul_neg, ← D.integral_comp_comm, ← integral_smul]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun t => (integrand_add z v s t).symm)
  change -(∫ s in Ioi (0 : ℝ), burnolDirectRightResolventIntegrand z (burnolDirectRightResolvent z v) s) = _
  simp_rw [acted, integral_neg, neg_neg]
  exact positive_time_triangle f (integrand_square_integrable z right v)

/-- The first log moment is generated by two full inward steps of the same original resolvent. -/
theorem directLogMoment_eq_half_square (z : ℂ) (right : 1 / 4 < z.re) (v : BurnolL2) :
    directLogMoment z v = (1 / 2 : ℂ) • burnolDirectRightResolvent z (burnolDirectRightResolvent z v) := by
  rw [directLogMoment, square_integral z right, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with r
  have scale : ((r / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) * (r : ℂ) := by push_cast; ring
  let integrand := burnolDirectRightResolventIntegrand z v r
  change ((r / 2 : ℝ) : ℂ) • integrand = (1 / 2 : ℂ) • (r • integrand)
  calc
    _ = ((1 / 2 : ℂ) * (r : ℂ)) • integrand := congrArg (· • integrand) scale
    _ = (1 / 2 : ℂ) • ((r : ℂ) • integrand) := (smul_smul _ _ _).symm
    _ = _ := congrArg ((1 / 2 : ℂ) • ·)
      (RCLike.real_smul_eq_coe_smul (K := ℂ) r integrand).symm

private theorem right_quarter (c : BurnolCompletedMellinCoordinate) : 1 / 4 < (c.value / 2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [c.rightHalf]

/-- The position log keeps the inward time-moment correction. -/
def positionLogAfter (c : BurnolCompletedMellinCoordinate) (x log : BurnolL2) : BurnolL2 :=
  C c log - ((δ c / 2 : ℝ) : ℂ) • R c (R c x)

/-- The inverse-Fourier log keeps the opposite correction from the same full action. -/
def frequencyLogAfter (c : BurnolCompletedMellinCoordinate) (x log : BurnolL2) : BurnolL2 :=
  fourierL2.symm (C c (F log) + ((δ c / 2 : ℝ) : ℂ) • R c (R c x))

private theorem position_log (c : BurnolCompletedMellinCoordinate) {x log : BurnolL2}
    (source : LogPair x log) : LogPair (C c x) (positionLogAfter c x log) := by
  have acted := actual_direct_R_log (c.value / 2) (right_quarter c) _ _ source
  rw [directLogMoment_eq_half_square (c.value / 2) (right_quarter c)] at acted
  change LogPair (R c x) (R c log - (1 / 2 : ℂ) • R c (R c x)) at acted
  have joined := log_pair_add _ _ _ _ source (logPair_smul (δ c : ℂ) _ _ acted)
  have half : (δ c : ℂ) * (1 / 2 : ℂ) = ((δ c / 2 : ℝ) : ℂ) := by push_cast; ring
  change LogPair (C c x) (log + (δ c : ℂ) • (R c log - (1 / 2 : ℂ) • R c (R c x))) at joined
  change LogPair (C c x)
    (log + (δ c : ℂ) • R c log - ((δ c / 2 : ℝ) : ℂ) • R c (R c x))
  simpa only [smul_sub, smul_smul, half, add_sub_assoc] using joined

private theorem cayley_graph (c : BurnolCompletedMellinCoordinate) {x gamma : BurnolL2}
    (source : GammaPair x gamma) : GammaPair (C c x) (C c gamma) := by
  have acted := actual_Gamma_R c _ _ source
  intro test
  change inner ℂ (wholeConductorTest test) (x + (δ c : ℂ) • R c x) =
    inner ℂ (test.toLp 2 volume) (gamma + (δ c : ℂ) • R c gamma)
  simp only [inner_add_right, inner_smul_right, source test, acted test]

private theorem weighted_square_pair (c : BurnolCompletedMellinCoordinate) (x y : BurnolL2) :
    (δ c : ℂ) * inner ℂ (R c (R c x)) (C c y) = -(δ c : ℂ) * inner ℂ (R c x) (R c y) := by
  have paired := sourceCayley_inner c (R c x) y
  change inner ℂ (R c x + (δ c : ℂ) • R c (R c x)) (C c y) = inner ℂ (R c x) y at paired
  have first : inner ℂ (R c x) (C c y) = inner ℂ (R c x) y + (δ c : ℂ) * inner ℂ (R c x) (R c y) := by
    change inner ℂ (R c x) (y + (δ c : ℂ) • R c y) = _
    rw [inner_add_right, inner_smul_right]
  rw [inner_add_left, inner_smul_left, show (starRingEnd ℂ) (δ c : ℂ) = (δ c : ℂ) from Complex.conj_ofReal _, first] at paired
  linear_combination paired

/-- The same full Cayley action generates both log fields and opposite directed work on any second input. -/
theorem actual_Cayley_log_clock (c : BurnolCompletedMellinCoordinate) (x logX freqX y : BurnolL2)
    (position : LogPair x logX) (frequency : LogPair (fourierL2.symm x) freqX) :
    LogPair (C c x) (positionLogAfter c x logX) ∧
    LogPair (fourierL2.symm (C c x)) (frequencyLogAfter c x freqX) ∧
    inner ℂ (positionLogAfter c x logX) (C c y) =
      inner ℂ logX y + ((δ c / 2 : ℝ) : ℂ) * inner ℂ (R c x) (R c y) ∧
    inner ℂ (F (frequencyLogAfter c x freqX)) (C c y) =
      inner ℂ (F freqX) y - ((δ c / 2 : ℝ) : ℂ) * inner ℂ (R c x) (R c y) := by
  have logged := position_log c position
  have complete := cayley_graph c (gamma_pair_of_log_pairs _ _ _ position frequency)
  have freq := inverse_log_from_complete_source _ _ _ complete logged
  have sum : C c (logX + F freqX) - positionLogAfter c x logX =
      C c (F freqX) + ((δ c / 2 : ℝ) : ℂ) • R c (R c x) := by
    rw [positionLogAfter, map_add]
    abel
  rw [sum] at freq
  refine ⟨logged, freq, ?_, ?_⟩
  · rw [positionLogAfter, inner_sub_left, inner_smul_left, sourceCayley_inner,
      show (starRingEnd ℂ) ((δ c / 2 : ℝ) : ℂ) = ((δ c / 2 : ℝ) : ℂ) from Complex.conj_ofReal _]
    push_cast
    linear_combination (-1 / 2 : ℂ) * weighted_square_pair c x y
  · rw [frequencyLogAfter, LinearIsometryEquiv.apply_symm_apply, inner_add_left,
      inner_smul_left, sourceCayley_inner,
      show (starRingEnd ℂ) ((δ c / 2 : ℝ) : ℂ) = ((δ c / 2 : ℝ) : ℂ) from Complex.conj_ofReal _]
    push_cast
    linear_combination (1 / 2 : ℂ) * weighted_square_pair c x y

end OriginalRSourceJointContact.CayleyLogClock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
