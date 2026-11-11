import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaIterated.Position
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaIterated.Frequency

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.KGamma.Iterated

open Complex Filter FourierTransform MeasureTheory
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.JointLogConductor
open OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.CountingQuadraticLimit OriginalGamma.Source.ConductorDual
open OriginalGamma.Source.GammaSeedExterior

open private gamma_pair_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource

noncomputable section
local notation "F" => fourierL2
local notation "K" => burnolCompletedMellinRieszVector

def actualSecondGammaSeed : BurnolL2 :=
  actualGammaSeedPositionLog + F actualGammaSeedFrequencyLog

theorem actual_second_gamma_seed :
    GammaPair actualGammaSeed actualSecondGammaSeed :=
  gamma_pair_of_log_pairs _ _ _ actual_gamma_seed_position_log actual_gamma_seed_frequency_log

/-- The original base and B syntheses act on the second conductor value of the same seed. -/
def actualSecondGammaKernel (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  originalBaseSynthesis c actualSecondGammaSeed - F (originalBSynthesis c actualSecondGammaSeed)

theorem actual_second_gamma_kernel (c : BurnolCompletedMellinCoordinate) :
    GammaPair (actualGammaKernel c) (actualSecondGammaKernel c) := by
  have base := (phiGammaPaid% gamma_pair_base) c _ _ actual_second_gamma_seed
  have b := gamma_pair_fourier _ _ ((phiGammaPaid% gamma_pair_b) c _ _ actual_second_gamma_seed)
  intro test
  rw [actualGammaKernel, inner_sub_right, base test, b test, actualSecondGammaKernel, inner_sub_right]

def actualGammaKernelPositionLog (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (kGammaDualPaid% basePositionLog) c actualGammaSeed actualGammaSeedPositionLog -
    (kGammaDualPaid% bFrequencyLog) c actualGammaSeed actualGammaSeedFrequencyLog

def actualGammaKernelFrequencyLog (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2.symm (actualSecondGammaKernel c - actualGammaKernelPositionLog c)

private theorem actual_gamma_kernel_position_log (c : BurnolCompletedMellinCoordinate) :
    LogPair (actualGammaKernel c) (actualGammaKernelPositionLog c) := by
  have base := (kGammaDualPaid% base_position_log_source) c actualGammaSeed
    actualGammaSeedPositionLog actual_gamma_seed_position_log
  have b := (kGammaDualPaid% b_frequency_log_source) c actualGammaSeed
    actualGammaSeedFrequencyLog actual_gamma_seed_frequency_log
  have evenB : reflectL2 (originalBSynthesis c actualGammaSeed) = originalBSynthesis c actualGammaSeed := by
    change reflectL2.toContinuousLinearMap (originalBSynthesis c actualGammaSeed) = _
    rw [(forwardFirstPaid% b_commute) c reflectL2.toContinuousLinearMap
      reflectL2_burnolMultiplicativeDilation]
    change originalBSynthesis c (reflectL2 actualGammaSeed) = _
    rw [actual_gamma_seed_even]
  have inverseB : fourierL2.symm (originalBSynthesis c actualGammaSeed) = F (originalBSynthesis c actualGammaSeed) := by
    rw [fourierL2_symm_eq_reflect_fourierL2, ← fourierL2_reflectL2_commute, evenB]
  rw [inverseB] at b
  exact (dualFourierPaid% logPair_sub) _ _ _ _ base b

theorem actual_gamma_kernel_complete_log_sources (c : BurnolCompletedMellinCoordinate) :
    LogPair (actualGammaKernel c) (actualGammaKernelPositionLog c) ∧
      LogPair (fourierL2.symm (actualGammaKernel c)) (actualGammaKernelFrequencyLog c) := by
  refine ⟨actual_gamma_kernel_position_log c, ?_⟩
  apply kGammaDualPaid% log_pair_of_weak
  intro test
  have gamma := actual_second_gamma_kernel c (𝓕 test)
  have position := (dualStrongPaid% log_pair_pairing) _ _ _ _
    (original_log_schwartz_domain (𝓕 test)) (actual_gamma_kernel_position_log c)
  rw [wholeConductorTest, inner_add_left, position, FourierTransform.fourierInv_fourier_eq] at gamma
  rw [← SchwartzMap.toLp_fourier_eq] at gamma
  change inner ℂ (F (test.toLp 2 volume)) (actualGammaKernelPositionLog c) +
    inner ℂ (F (logSchwartzL2 test)) (actualGammaKernel c) =
    inner ℂ (F (test.toLp 2 volume)) (actualSecondGammaKernel c) at gamma
  rw [fourierL2.inner_map_eq_flip, fourierL2.inner_map_eq_flip, fourierL2.inner_map_eq_flip] at gamma
  rw [actualGammaKernelFrequencyLog, map_sub, inner_sub_right]
  linear_combination gamma

end
end OriginalGamma.Source.KGamma.Iterated
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
