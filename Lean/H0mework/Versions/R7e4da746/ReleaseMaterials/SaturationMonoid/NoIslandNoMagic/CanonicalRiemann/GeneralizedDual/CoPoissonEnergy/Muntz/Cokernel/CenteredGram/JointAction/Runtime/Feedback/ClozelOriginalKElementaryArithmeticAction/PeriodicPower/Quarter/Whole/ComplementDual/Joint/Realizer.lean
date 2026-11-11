import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Remainder
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Forward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Resolvent

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Realizer
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Remainder OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Forward
open scoped Topology
open private actual_fourier_linear_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.FourierQuarter
open private realizes_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Resolvent

private theorem dual_forward (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (x:ℝ):
    burnolInnerGapForward (dualFourierRaw c) x=countFourierRaw c zero x-
      2*deriv (poleFreeSource c) 1/(1-star c.value):=by
  have reindex:burnolInnerGapForward (dualFourierRaw c) x=
      ∑'n:ℕ,((n+1:ℕ):ℂ)⁻¹*dualFourierRaw c (x/(n+1:ℕ)):=
    (Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
      (fun n:ℕ+=>((n:ℕ):ℂ)⁻¹*dualFourierRaw c (x/(n:ℕ)))).symm
  rw [reindex]
  exact (actual_complete_fourier_source c zero x).tsum_eq

/-- The true reciprocal mean cancels the counted origin mass on the entire comb, for every test. -/
theorem actual_dual_remainder (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (test:SchwartzMap ℝ ℂ):
    (1/2:ℂ)*(∫x:ℝ,dualFourierRaw c x*coPoissonMuntzScaleRemainder test |x|)=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 (fullFloorValue c zero))) test:=by
  have origin:dualFourierRaw c 0=0:=norm_eq_zero.mp (le_antisymm (by
    simpa only [dualFourierRaw,abs_zero,mul_zero] using actual_fourier_linear_bound c 0) (norm_nonneg _))
  have actual:=actual_regular_remainder_forward (dualFourierRaw c)
    (actual_fourier_continuous _ (actual_dual_integrable c.value c.belowOne)).measurable
    origin (actual_dual_fourier_even c) (frequencyBound c) (actual_fourier_linear_bound c)
    (actual_reciprocal_integrable c) test (actual_dual_fourier_remainder_integrable c test)
  change _=∫x:ℝ,test x*(burnolInnerGapForward (dualFourierRaw c) x-dualReciprocalMean c) at actual
  rw [actual,Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [actual_L2_fourier_raw c zero] with x raw
  rw [dual_forward c zero x,actual_dual_reciprocal_mean c zero,raw]
  simp only [sub_neg_eq_add,sub_add_cancel,smul_eq_mul]

def jointValue (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):BurnolL2:=
  wholeValue c zero h positive+fourierL2 (fullFloorValue c zero)

/-- One actual L2 source realizes the complete joint field, with both Unit terms already paid. -/
theorem actual_joint_realizes (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (jointSource c) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (jointValue c zero h positive)) test:=by
  rw [actual_joint_remainder c zero h positive test,actual_dual_remainder c zero test,
    jointValue,map_add]
  rfl

/-- Actual R acts before all projections, on the same complete source and the same complete value. -/
theorem actual_joint_R_power (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ) (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (((burnolDirectRightResolventCLM c)^j) (jointSource c)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (((burnolDirectRightResolventCLM c)^j) (jointValue c zero h positive))) test:=
  realizes_power c _ _ (actual_joint_realizes c zero h positive) j test

/-- The original owner and its actual Xi order read this same full source. -/
theorem actual_joint_original_order (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (test:SchwartzMap ℝ ℂ):
    let observation:=burnolPaZeroObservation c zero
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    burnolRemainderSourceRead (CombSource.Division.rawIterate observation c.rightHalf m (jointSource c)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (CombSource.Division.rawIterate observation c.rightHalf m (jointValue c zero h positive))) test:=by
  dsimp only
  have same:burnolDivisionZeroCompletedMellinCoordinate (burnolPaZeroObservation c zero) c.rightHalf=c:=by
    cases c
    rfl
  simp only [CombSource.Division.rawIterate,CombSource.Division.rawAction,same]
  exact actual_joint_R_power c zero h positive _ test

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Realizer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
