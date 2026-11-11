import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitRegularity.GeneratorCounting
import H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.Source.Division.Whole

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Resolvent
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open scoped Topology InnerProductSpace
open private resolvent_realizes from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitRegularity.GeneratorCounting

private theorem realizes_power (c : BurnolCompletedMellinCoordinate) (source value : BurnolL2)
    (realizes : ∀test:SchwartzMap ℝ ℂ,burnolRemainderSourceRead source test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) (j : ℕ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (((burnolDirectRightResolventCLM c)^j) source) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (((burnolDirectRightResolventCLM c)^j) value)) test := by
  induction j generalizing test with
  | zero => simpa only [pow_zero,one_apply_eq_self] using realizes test
  | succ j hypothesis =>
      rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp]
      exact resolvent_realizes (c.value/2) (by
        rw [Complex.div_re]
        norm_num
        linarith [c.rightHalf]) _ _ (fun ψ=>hypothesis ψ) test

/-- The actual full co-Poisson realization commutes with every original R power, including all Unit components. -/
theorem actual_whole_R_power (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (j : ℕ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (((burnolDirectRightResolventCLM c)^j) (quarterWave c)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (((burnolDirectRightResolventCLM c)^j) (wholeValue c zero h positive))) test :=
  realizes_power c _ _ (actual_whole_realizes c zero h positive) j test

theorem actual_difference_R_power (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (j : ℕ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (((burnolDirectRightResolventCLM c)^j) (waveDifference c h)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (((burnolDirectRightResolventCLM c)^j) (fourierL2 (countedValue c zero h nonnegative)))) test :=
  realizes_power c _ _ (actual_difference_realizes c zero h nonnegative) j test

theorem actual_whole_R_action (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (j : ℕ) (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
      (burnolMultiplicativeDilation shift (((burnolDirectRightResolventCLM c)^j) (quarterWave c))) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolMultiplicativeDilation shift
        (((burnolDirectRightResolventCLM c)^j) (wholeValue c zero h positive)))) test :=
  burnolRemainderRealization_dilation _ _ (actual_whole_R_power c zero h positive j) shift test

/-- This is the exact original owner/observation/order consumed by UnitPowerSource.actual_full_power_read. -/
theorem actual_original_order_realizes (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (test : SchwartzMap ℝ ℂ) :
    let observation:=burnolPaZeroObservation c zero
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    burnolRemainderSourceRead
      (CombSource.Division.rawIterate observation c.rightHalf m (quarterWave c)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (CombSource.Division.rawIterate observation c.rightHalf m (wholeValue c zero h positive))) test := by
  dsimp only
  have same:burnolDivisionZeroCompletedMellinCoordinate (burnolPaZeroObservation c zero) c.rightHalf=c := by
    cases c
    rfl
  simp only [CombSource.Division.rawIterate,CombSource.Division.rawAction,same]
  exact actual_whole_R_power c zero h positive _ test

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
