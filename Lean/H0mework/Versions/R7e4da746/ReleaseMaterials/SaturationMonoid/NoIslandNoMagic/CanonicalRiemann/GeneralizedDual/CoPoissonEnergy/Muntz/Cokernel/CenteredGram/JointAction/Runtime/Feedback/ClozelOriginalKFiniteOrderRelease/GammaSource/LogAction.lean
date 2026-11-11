import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.Continuity

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.LogAction
open Complex Filter MeasureTheory Set
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.LogPairClosure
open private logPair_dilation logPair_smul from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource

def directLogMoment (z : ℂ) (v : BurnolL2) : BurnolL2 :=
  ∫ t : ℝ in Ioi 0, ((t / 2 : ℝ) : ℂ) • burnolDirectRightResolventIntegrand z v t

private theorem moment_integrable (z : ℂ) (right : 1 / 4 < z.re) (v : BurnolL2) :
    IntegrableOn (fun t : ℝ => ((t / 2 : ℝ) : ℂ) •
      burnolDirectRightResolventIntegrand z v t) (Ioi 0) := by
  let a := z.re - 1 / 4
  have positive : 0 < a := sub_pos.mpr right
  have envelope : IntegrableOn (fun t : ℝ => Real.exp (-(a / 2) * t) * (‖v‖ / a)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (half_pos positive)).mul_const _
  have continuous : Continuous (fun t : ℝ => ((t / 2 : ℝ) : ℂ) •
      burnolDirectRightResolventIntegrand z v t) := by
    unfold burnolDirectRightResolventIntegrand
    exact (by fun_prop : Continuous fun t : ℝ => ((t / 2 : ℝ) : ℂ)).smul
      ((positiveMellinQuarterRightResolventWeight_continuous z).smul
        ((burnolMultiplicativeDilation_stronglyContinuous v).comp (by fun_prop)))
  apply Integrable.mono' envelope continuous.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t time
  have timePositive : 0 < t := time
  have clock : t / 2 ≤ Real.exp ((a / 2) * t) / a := by
    apply (le_div_iff₀ positive).mpr
    have bound := Real.add_one_le_exp ((a / 2) * t)
    nlinarith
  have joined : Real.exp ((a / 2) * t) * Real.exp (-a * t) =
      Real.exp (-(a / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖((t / 2 : ℝ) : ℂ) • burnolDirectRightResolventIntegrand z v t‖ =
        (t / 2) * (Real.exp (-a * t) * ‖v‖) := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos timePositive), burnolDirectRightResolventIntegrand,
        norm_smul, (burnolMultiplicativeDilation (-t / 2)).norm_map,
        norm_positiveMellinQuarterRightResolventWeight, a]
    _ ≤ (Real.exp ((a / 2) * t) / a) * (Real.exp (-a * t) * ‖v‖) :=
      mul_le_mul_of_nonneg_right clock (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    _ = Real.exp (-(a / 2) * t) * (‖v‖ / a) := by
      calc
        _ = (Real.exp ((a / 2) * t) * Real.exp (-a * t)) * (‖v‖ / a) := by ring
        _ = _ := by rw [joined]

/-- The actual inward dilation clock pays its logarithmic commutator as a first time moment. -/
theorem actual_direct_R_log (z : ℂ) (right : 1 / 4 < z.re)
    (v logarithm : BurnolL2) (source : LogPair v logarithm) :
    LogPair (burnolDirectRightResolvent z v)
      (burnolDirectRightResolvent z logarithm - directLogMoment z v) := by
  have first := burnolDirectRightResolventIntegrand_integrableOn z right v
  have logged := burnolDirectRightResolventIntegrand_integrableOn z right logarithm
  have moment := moment_integrable z right v
  have actual : ∀ t : ℝ, LogPair (burnolDirectRightResolventIntegrand z v t)
      (burnolDirectRightResolventIntegrand z logarithm t +
        ((t / 2 : ℝ) : ℂ) • burnolDirectRightResolventIntegrand z v t) := by
    intro t
    have pair := logPair_smul (positiveMellinQuarterRightResolventWeight z t) _ _
      (logPair_dilation (-t / 2) v logarithm source)
    have read : positiveMellinQuarterRightResolventWeight z t •
        (burnolMultiplicativeDilation (-t / 2) logarithm -
          ((-t / 2 : ℝ) : ℂ) • burnolMultiplicativeDilation (-t / 2) v) =
        burnolDirectRightResolventIntegrand z logarithm t +
          ((t / 2 : ℝ) : ℂ) • burnolDirectRightResolventIntegrand z v t := by
      unfold burnolDirectRightResolventIntegrand
      push_cast
      module
    rw [read] at pair
    exact pair
  have generated := logPair_integral (volume.restrict (Ioi 0)) _ _ first
    (logged.add moment) (Eventually.of_forall actual)
  have negative := logPair_smul (-1 : ℂ) _ _ generated
  simp only [Pi.add_apply] at negative
  rw [integral_add logged moment] at negative
  simpa only [neg_one_smul, neg_add, sub_eq_add_neg,
    burnolDirectRightResolvent, directLogMoment] using negative

end OriginalRSourceJointContact.LogAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
