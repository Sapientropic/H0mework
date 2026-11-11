import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.LogDomains
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PaCoefficient
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PositiveKernelEven
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaForwardCountKPriceSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaForwardCountPhiSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.WholeCoefficient
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.KappaConductor
open OriginalGamma.Source.GammaForwardCountPhi OriginalGamma.Source.PhiConductorReadback
open OriginalGamma.Source.ConductorDual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PaCoefficient OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutLog
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.LogDomains
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PositiveKernelEven
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.NativePa
open scoped InnerProductSpace Topology
open private forwardGammaPositionLog forwardGammaFrequencyLog
  actual_forward_gamma_position_log_source actual_forward_gamma_frequency_log_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaForwardCountKPriceSource
open private Gamma_unique from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
local notation "K" => burnolCompletedMellinRieszVector
local notation "F" => fourierL2
local notation "D" => CountingDual.sourceCLM
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- Both logarithmic domains and both Gamma values come from the actual source before the price is moved. -/
theorem actual_original_finite_log_Gamma_price (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    inner ℂ (logGamma (barC c)) (F (D N (K c : BurnolL2))) =
      inner ℂ (logValue (barC c)) (F (D N (actualGammaKernel c))) :=
  whole_conductor_dual _ _ _ _ _ _ _ _
    (actual_log_Gamma (barC c))
    ((programmeGammaFourierPaid% gamma_pair_fourier) _ _
      (actual_original_forward_gamma_kernel_count_source c N))
    (actual_log_two_sources (barC c)).1 (actual_log_two_sources (barC c)).2
    (actual_forward_gamma_position_log_source c N) (actual_forward_gamma_frequency_log_source c N)

/-- The original strong K count pays this whole Gamma read without assuming a strong Gamma count. -/
theorem actual_original_log_Gamma_whole_price
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Tendsto (fun N : ℕ => inner ℂ (logValue (barC c)) (F (D N (actualGammaKernel c)))) atTop
      (𝓝 (inner ℂ (logValue (barC c)) (originalDualLogValue c))) := by
  have source := (tendsto_const_nhds (x := logGamma (barC c))).inner (𝕜 := ℂ)
    (actual_original_fourier_forward_K_whole_source c zero)
  have complete := whole_conductor_dual _ _ _ _ _ _ _ _
    (actual_log_Gamma (barC c)) (original_dual_field_conductor c zero)
    (actual_log_two_sources (barC c)).1 (actual_log_two_sources (barC c)).2
    (original_dual_field_log_pairs c zero).1 (original_dual_field_log_pairs c zero).2
  rw [complete] at source
  apply source.congr'
  exact Eventually.of_forall (fun N => actual_original_finite_log_Gamma_price c N)

private theorem limiting_Gamma_even
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    reflectL2 (originalDualLogValue c) = originalDualLogValue c := by
  have source := original_dual_field_conductor c zero
  have doubled := (programmeGammaFourierPaid% gamma_pair_fourier) _ _
    ((programmeGammaFourierPaid% gamma_pair_fourier) _ _ source)
  rw [fourierL2_fourierL2, fourierL2_fourierL2,
    (programmeForwardPaid% actual_dual_even) c zero] at doubled
  exact Gamma_unique _ _ _ doubled source

/-- The original positive synthesis coefficient is now the whole-source Gamma cotest on the actual strong K count. -/
theorem actual_finite_Gamma_Pa_whole_coefficient (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    burnolPaResolventSourceCoefficient c (finitePa c N) =
      (1/2 : ℂ) * inner ℂ (logGamma (barC c)) (F (D N (K c : BurnolL2))) := by
  rw [actual_finite_Gamma_Pa_coefficient, actual_finite_positive_log_kernel_read,
    actual_original_finite_log_Gamma_price]

theorem actual_limiting_Gamma_Pa_whole_coefficient
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    burnolPaResolventSourceCoefficient c (limitingPa c) =
      (1/2 : ℂ) * inner ℂ (logGamma (barC c)) (originalDualField c zero) := by
  rw [actual_limiting_Gamma_Pa_coefficient,
    actual_positive_log_kernel_even_read c _ (limiting_Gamma_even c zero)]
  rw [whole_conductor_dual _ _ _ _ _ _ _ _
    (actual_log_Gamma (barC c)) (original_dual_field_conductor c zero)
    (actual_log_two_sources (barC c)).1 (actual_log_two_sources (barC c)).2
    (original_dual_field_log_pairs c zero).1 (original_dual_field_log_pairs c zero).2]

/-- This complete coefficient limit is paid by the original strong K count, with no strong Gamma field as an input. -/
theorem actual_original_Gamma_Pa_coefficient_whole_source
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Tendsto (fun N : ℕ => burnolPaResolventSourceCoefficient c (finitePa c N)) atTop
      (𝓝 (burnolPaResolventSourceCoefficient c (limitingPa c))) := by
  have source := ((tendsto_const_nhds (x := logGamma (barC c))).inner (𝕜 := ℂ)
    (actual_original_fourier_forward_K_whole_source c zero)).const_mul (1/2 : ℂ)
  rw [← actual_limiting_Gamma_Pa_whole_coefficient c zero] at source
  apply source.congr'
  exact Eventually.of_forall (fun N => (actual_finite_Gamma_Pa_whole_coefficient c N).symm)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
include nontrivial

/-- The same original owner/order consumes the actual bounded whole Gamma coefficient. -/
theorem actual_original_limiting_Gamma_whole_top_source :
    inner ℂ (sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (limitingPa c : BurnolL2)) =
        feedbackCoefficient observation half * ((1/2 : ℂ) *
          inner ℂ (logGamma (barC c)) (originalDualField c observation.mathlibZero)) := by
  have source := actual_limiting_Gamma_Pa_top observation nontrivial half
  rw [actual_limiting_Gamma_Pa_whole_coefficient c observation.mathlibZero] at source
  exact source

/-- The exact m top sequence now has its complete source-generated scalar limit. -/
theorem actual_original_Gamma_whole_top_tendsto :
    Tendsto (fun N : ℕ => inner ℂ (sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (finitePa c N : BurnolL2))) atTop
      (𝓝 (inner ℂ (sourceKernelCombo c)
        (CombSource.Division.rawIterate observation half.down m (limitingPa c : BurnolL2)))) := by
  have source := (actual_original_Gamma_Pa_coefficient_whole_source c observation.mathlibZero).const_mul
    (feedbackCoefficient observation half)
  rw [← actual_limiting_Gamma_Pa_top observation nontrivial half] at source
  apply source.congr'
  exact Eventually.of_forall (fun N => (actual_finite_Gamma_Pa_top observation nontrivial half N).symm)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.WholeCoefficient
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
