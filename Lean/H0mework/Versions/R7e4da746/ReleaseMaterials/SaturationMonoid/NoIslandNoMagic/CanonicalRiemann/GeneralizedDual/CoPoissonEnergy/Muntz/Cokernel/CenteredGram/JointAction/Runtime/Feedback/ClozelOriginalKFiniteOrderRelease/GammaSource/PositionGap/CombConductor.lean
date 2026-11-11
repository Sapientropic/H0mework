import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.CrossPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.TateGaussianClock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantFourier

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.CombConductor

open BurnolPhysicalState MeasureTheory
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.FiniteLogCounting
open OriginalGamma.Source.TateConductor OriginalGamma.Source.JointLogConductor
open scoped InnerProductSpace

open private gamma_pair_dilation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
open private gamma_pair_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
open private logPair_dilation logPair_smul logPair_sub from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource
open private position_from_frequency from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.CrossPrice

local notation "D" => burnolMultiplicativeDilation
local notation "S" => burnolSourceScalePrimitive
local notation "F" => fourierL2
local notation "counted" => burnolUnitCountingPrimitiveL2
local notation "tate" => burnolTateReciprocalL2 ConstantDual.value
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)

private theorem count_from_tate : S tate 4 = counted := by
  rw [ConstantFourier.reciprocal_value]
  simp only [burnolSourceScalePrimitive, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [map_smul, smul_smul, burnolMultiplicativeDilation_add]
  have scale : (Real.sqrt (4:ℝ) : ℂ) * (Real.sqrt (1/4:ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  have clock : Real.log 4 + Real.log (1/4) = 0 := by
    rw [← Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (1/4:ℝ) ≠ 0)]
    norm_num
  change ((Real.sqrt (4:ℝ) : ℂ) * (Real.sqrt (1/4:ℝ) : ℂ)) •
    D (Real.log 4 + Real.log (1/4)) counted = counted
  rw [scale, clock, burnolMultiplicativeDilation_zero, one_smul]

private def scaledPositionLog (value logged : BurnolL2) (scale : ℝ) : BurnolL2 :=
  (Real.sqrt scale : ℂ) •
    (D (Real.log scale) logged - (Real.log scale : ℂ) • D (Real.log scale) value)

private theorem scaled_position_graph (value logged : BurnolL2) (scale : ℝ)
    (source : LogPair value logged) : LogPair (S value scale) (scaledPositionLog value logged scale) := by
  exact logPair_smul _ _ _ (logPair_dilation _ _ _ source)

private theorem scaled_gamma_graph (value gamma : BurnolL2) (scale : ℝ)
    (source : GammaPair value gamma) : GammaPair (S value scale) (S gamma scale) := by
  intro test
  change inner ℂ (wholeConductorTest test) ((Real.sqrt scale : ℂ) • D (Real.log scale) value) =
    inner ℂ (test.toLp 2 volume) ((Real.sqrt scale : ℂ) • D (Real.log scale) gamma)
  simp only [inner_smul_right, gamma_pair_dilation _ _ _ source test]

private def countGamma : BurnolL2 := S tateFirstStrongConductor 4
private def countLog : BurnolL2 := scaledPositionLog tate tateFirstLog 4

private theorem count_gamma_graph : GammaPair counted countGamma := by
  rw [← count_from_tate]
  exact scaled_gamma_graph _ _ _ original_tate_strong_conductor

private theorem count_position_graph : LogPair counted countLog := by
  rw [← count_from_tate]
  exact scaled_position_graph _ _ _ original_tate_first_log

private theorem literal_comb_seed :
    seed = (2 : ℂ) • F (S counted (3/2) - counted) := by
  rw [burnolPaCombApproximation_raw]
  norm_num [burnolPaCombSourceWidth, burnolReciprocalStepNativeWave, burnolSourceScalePrimitive,
    burnolMultiplicativeDilation_zero]

/-- The conductor is generated by the two actual endpoints of the original comb scale band. -/
def seedGamma : BurnolL2 := (2 : ℂ) • F (S countGamma (3/2) - countGamma)

def seedInverseLog : BurnolL2 := (2 : ℂ) • (scaledPositionLog counted countLog (3/2) - countLog)

def seedPositionLog : BurnolL2 := seedGamma - F seedInverseLog

theorem actual_comb_seed_gamma : GammaPair seed seedGamma := by
  have scaled := scaled_gamma_graph _ _ (3/2) count_gamma_graph
  have band : GammaPair (S counted (3/2) - counted) (S countGamma (3/2) - countGamma) := by
    intro test
    rw [inner_sub_right, inner_sub_right, scaled test, count_gamma_graph test]
  have fourier := gamma_pair_fourier _ _ band
  intro test
  rw [literal_comb_seed, seedGamma, inner_smul_right, inner_smul_right, fourier test]

theorem actual_comb_seed_inverse_log : LogPair (fourierL2.symm seed) seedInverseLog := by
  rw [literal_comb_seed, map_smul, fourierL2.symm_apply_apply]
  exact logPair_smul _ _ _ (logPair_sub _ _ _ _
    (scaled_position_graph _ _ _ count_position_graph) count_position_graph)

theorem actual_comb_seed_position_log : LogPair seed seedPositionLog :=
  position_from_frequency _ _ _ actual_comb_seed_gamma actual_comb_seed_inverse_log

end OriginalKFiniteOrderRelease.PositionGapCayley.CombConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
