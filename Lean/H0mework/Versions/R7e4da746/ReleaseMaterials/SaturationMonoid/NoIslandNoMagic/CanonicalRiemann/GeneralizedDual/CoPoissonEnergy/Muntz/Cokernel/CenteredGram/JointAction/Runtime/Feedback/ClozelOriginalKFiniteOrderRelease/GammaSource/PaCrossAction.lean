import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Quadratic

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRSourceJointContact.PaCrossAction
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.KappaConductor
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.ConductorDual
open OriginalGamma.Source.GammaKernelWholeWeakCount OriginalGamma.Source.GammaFirstCountingConductor
open OriginalGamma.Source.CountedPositionTateGamma
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.TateWindow
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PaCut
open scoped InnerProductSpace Topology
open private counted_kernel_position_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaUnitFourierClockKPriceSource
open private inverse_log_from_complete_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
open private dual_tate from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open private annulus_pair from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
local notation "K" => burnolCompletedMellinRieszVector
local notation "T" => burnolTateReciprocalL2
local notation "ν" => burnolMobiusSourceL2
local notation "AN" => FiniteForcing.source
local notation "DN" => DualSource.source
local notation "A" => sourceAnnulusCut
local notation "V" => sourceVolterraResolvent

private theorem actual_nu_forward
    (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) (even : reflectL2 value = value) :
    Tendsto (fun N : Nat => AN N (tateWindow c value)) atTop
      (𝓝 (sourceVolterraPhysical c value : BurnolL2)) := by
  have reverse := actual_volterra_reverse c (A value)
  have source := (burnolTateReciprocalL2.continuous.tendsto
    (T (sourceVolterraPhysical c (A value) : BurnolL2))).comp reverse
  rw [burnolTateReciprocalL2_involutive, sourceVolterraPhysical_annulus] at source
  apply source.congr'
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [dual_tate, burnolTateReciprocalL2_involutive, actual_tate_window_source c value even]

private theorem actual_finite_Gamma_nu_price
    (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) (even : reflectL2 value = value)
    (N : Nat) :
    inner ℂ (DN N (actualGammaKernel c)) (tateWindow c value) =
      inner ℂ (DN N (K c : BurnolL2)) (tateWindowGamma c value) := by
  have source := actual_original_gamma_kernel_complete_count c N
  have position := counted_kernel_position_source c N
  have frequency := inverse_log_from_complete_source _ _ _ source position
  have logs := actual_tate_window_two_sources c value even
  exact whole_conductor_dual _ _ _ _ _ _ _ _ source
    (actual_tate_window_Gamma c value even) position frequency logs.1 logs.2

private theorem actual_Gamma_nu_price_limit
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (value : BurnolL2) (even : reflectL2 value = value) :
    Tendsto (fun N : Nat => inner ℂ (DN N (actualGammaKernel c)) (tateWindow c value)) atTop
      (𝓝 (inner ℂ (originalFirstFieldGamma c) (tateWindow c value))) := by
  have source := (KCounting.original_tendsto c zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := tateWindowGamma c value))
  change Tendsto _ atTop
    (𝓝 (inner ℂ (originalFirstField c zero) (tateWindowGamma c value))) at source
  have logs := actual_tate_window_two_sources c value even
  have complete := whole_conductor_dual _ _ _ _ _ _ _ _
    (actual_original_first_field_complete_Gamma_source c zero)
    (actual_tate_window_Gamma c value even)
    (actual_original_first_field_complete_log_sources c zero).1
    (actual_original_first_field_complete_log_sources c zero).2 logs.1 logs.2
  rw [← complete] at source
  apply source.congr'
  exact Eventually.of_forall (fun N => (actual_finite_Gamma_nu_price c value even N).symm)

/-- The original Gamma kernel reads the physical Pa synthesis through its complete source wave. -/
theorem actual_original_Gamma_Pa_cross_source
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (value : BurnolL2) (even : reflectL2 value = value) :
    inner ℂ (actualGammaKernel c) (sourceVolterraPhysical c value : BurnolL2) =
      inner ℂ (A (originalDualLogValue c)) (V c (A value)) := by
  have left := (tendsto_const_nhds (x := actualGammaKernel c)).inner (𝕜 := ℂ)
    (actual_nu_forward c value even)
  have same : Tendsto (fun N : Nat => inner ℂ (DN N (actualGammaKernel c))
      (tateWindow c value)) atTop
      (𝓝 (inner ℂ (actualGammaKernel c) (sourceVolterraPhysical c value : BurnolL2))) := by
    apply left.congr'
    apply Eventually.of_forall
    intro N
    exact (ContinuousLinearMap.adjoint_inner_left (CountingDual.sourceCLM N)
      (tateWindow c value) (actualGammaKernel c)).symm.trans
        (by rw [← CountingDual.dual_eq_adjoint])
  have price := tendsto_nhds_unique same (actual_Gamma_nu_price_limit c zero value even)
  change inner ℂ (actualGammaKernel c) (sourceVolterraPhysical c value : BurnolL2) =
    inner ℂ (originalFirstFieldGamma c) (T (A (V c (A value)))) at price
  rw [← OriginalRieszFiniteSynthesis.tate_pairing,
    actual_original_counted_first_dual_same_Gamma_occurrence c zero, ← annulus_pair] at price
  exact price

end OriginalRSourceJointContact.PaCrossAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
