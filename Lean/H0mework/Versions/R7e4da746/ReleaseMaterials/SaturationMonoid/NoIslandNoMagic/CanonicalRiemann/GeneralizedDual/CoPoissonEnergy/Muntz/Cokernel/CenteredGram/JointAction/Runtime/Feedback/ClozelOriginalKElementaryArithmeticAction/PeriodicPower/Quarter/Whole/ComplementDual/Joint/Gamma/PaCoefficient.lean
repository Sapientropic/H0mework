import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.NativePa
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PaCoefficient
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.NativePa OriginalGamma.Source.KGamma OriginalGamma.Source.KappaConductor
open scoped InnerProductSpace Topology
open private sourceLogKernel_read sourceLogWeight_memLp from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
open private annulus_pair from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
local notation "q" => (1 / 4 : ℝ)
local notation "A" => sourceAnnulusCut

local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The actual Bochner shells pay the full coefficient, including the original log clock. -/
theorem actual_synthesis_coefficient (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    burnolPaResolventSourceCoefficient c (sourceVolterraPhysical c value) =
      inner ℂ (sourceLogKernel c) value := by
  unfold sourceVolterraPhysical
  rw [← (burnolPaResolventSourceCoefficient c).integral_comp_comm
    (sourceVolterraPhysical_integrable c value), sourceLogKernel_read]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u inside
  dsimp only
  rw [map_smul, volterra_shell_source_coefficient c u inside]
  unfold volterraSourceDensity
  ring

private theorem source_log_kernel_cut (c : BurnolCompletedMellinCoordinate) :
    A (sourceLogKernel c) = sourceLogKernel c := by
  have raw := (sourceLogWeight_memLp c).coeFn_toLp
  apply Lp.ext
  filter_upwards [sourceAnnulusCut_coeFn (sourceLogKernel c), raw, volume.ae_ne q] with u cut represented apart
  change sourceLogKernel c u = (Icc q 4).indicator (sourceLogWeight c) u at represented
  rw [cut, represented]
  by_cases inside : u ∈ Icc q 4
  · have positive : 0 < u := by linarith [inside.1]
    have lower : q < u := lt_of_le_of_ne inside.1 apart.symm
    rw [indicator_of_mem inside, abs_of_pos positive, if_pos ⟨lower, inside.2⟩]
  · rw [indicator_of_notMem inside]
    split_ifs <;> rfl

private theorem source_log_kernel_read_cut (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (sourceLogKernel c) (A value) = inner ℂ (sourceLogKernel c) value := by
  rw [← annulus_pair, source_log_kernel_cut]

theorem actual_finite_Gamma_Pa_coefficient (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    burnolPaResolventSourceCoefficient c (finitePa c N) =
      inner ℂ (sourceLogKernel c) (fourierL2 (CountingDual.sourceCLM N (actualGammaKernel c))) := by
  change burnolPaResolventSourceCoefficient c
    (sourceVolterraPhysical c (A (fourierL2 (CountingDual.sourceCLM N (actualGammaKernel c)))) ) = _
  rw [actual_synthesis_coefficient, source_log_kernel_read_cut]

theorem actual_limiting_Gamma_Pa_coefficient (c : BurnolCompletedMellinCoordinate) :
    burnolPaResolventSourceCoefficient c (limitingPa c) =
      inner ℂ (sourceLogKernel c) (originalDualLogValue c) := by
  change burnolPaResolventSourceCoefficient c (sourceVolterraPhysical c (A (originalDualLogValue c))) = _
  rw [actual_synthesis_coefficient, source_log_kernel_read_cut]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
include nontrivial

/-- The original same-owner m consumer now reads the actual whole Gamma source at its computed bounded log kernel. -/
theorem actual_original_finite_Gamma_top_source (N : ℕ) :
    inner ℂ (sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (finitePa c N : BurnolL2)) =
        feedbackCoefficient observation half *
          inner ℂ (sourceLogKernel c) (fourierL2 (CountingDual.sourceCLM N (actualGammaKernel c))) := by
  have source := actual_finite_Gamma_Pa_top observation nontrivial half N
  rw [actual_finite_Gamma_Pa_coefficient] at source
  exact source

theorem actual_original_limiting_Gamma_top_source :
    inner ℂ (sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (limitingPa c : BurnolL2)) =
        feedbackCoefficient observation half * inner ℂ (sourceLogKernel c) (originalDualLogValue c) := by
  have source := actual_limiting_Gamma_Pa_top observation nontrivial half
  rw [actual_limiting_Gamma_Pa_coefficient] at source
  exact source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PaCoefficient
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
