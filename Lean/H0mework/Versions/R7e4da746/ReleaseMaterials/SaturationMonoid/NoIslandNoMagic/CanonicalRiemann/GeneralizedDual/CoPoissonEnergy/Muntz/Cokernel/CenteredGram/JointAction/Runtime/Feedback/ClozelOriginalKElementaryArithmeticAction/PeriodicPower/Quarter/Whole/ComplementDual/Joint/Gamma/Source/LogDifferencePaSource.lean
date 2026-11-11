import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.DivisorJointSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FirstConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ForwardLogStepSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FourierLogDomainSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorStrongSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.WholePrimeLogSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContinuousChannels
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.Arithmetic.TruncatedFourier.Overlap
import H0mework.Versions.R7e4da746.Arithmetic.RiemannDivision.DirectRightResolvent
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Spectral.Direct.ClozelBurnolPaRiemannConsumer

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.LogDifferencePa
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalGamma.Source.KLogVector OriginalGamma.Source.FiniteLogCounting
open OriginalGamma.Source.CountingQuadraticLimit OriginalGamma.Source.CountingQuadratic
noncomputable section
local notation "q" => (1 / 4 : ℝ)
private theorem log_reflect (direction : ℝ) (N : ℕ) (value : BurnolL2) :
    reflectL2 (logCountingCLM direction N value) = logCountingCLM direction N (reflectL2 value) := by
  have channel (a : ℝ) : reflectL2 (logChannel direction a value) =
      logChannel direction a (reflectL2 value) := by
    simp only [logChannel, ContinuousChannels.channel, map_smul,
      reflectL2_burnolMultiplicativeDilation]
  simp only [logCountingCLM_apply, logProgramme, map_sub, map_sum]
  simp_rw [channel]
  congr 1
  calc
    reflectL2 (∫ a : ℝ in Ioc 0 (N : ℝ), logChannel direction a value) =
        ∫ a : ℝ in Ioc 0 (N : ℝ), reflectL2 (logChannel direction a value) :=
      (reflectL2.integral_comp_comm (fun a : ℝ => logChannel direction a value)).symm
    _ = _ := by simp_rw [channel]

private theorem seed_even : reflectL2 ConstantDual.seed = ConstantDual.seed := by
  change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q)) = _
  rw [burnolRadiusZeroExtension_reflect, reflectRestricted_intervalConstant]
  rfl

private theorem forward_log_even :
    reflectL2 OriginalGamma.Source.ForwardLogStep.logStepValue =
      OriginalGamma.Source.ForwardLogStep.logStepValue := by
  have reflected := (reflectL2.continuous.tendsto _).comp
    OriginalGamma.Source.ForwardLogStep.original_log_step_tendsto
  apply tendsto_nhds_unique reflected
  exact OriginalGamma.Source.ForwardLogStep.original_log_step_tendsto.congr'
    (Eventually.of_forall (fun N => by simp only [Function.comp_apply, LogA, log_reflect, seed_even]))

private theorem dual_log_even :
    reflectL2 OriginalGamma.Source.WholePrimeLog.logStepValue =
      OriginalGamma.Source.WholePrimeLog.logStepValue := by
  have reflected := (reflectL2.continuous.tendsto _).comp
    OriginalGamma.Source.WholePrimeLog.original_log_step_tendsto
  apply tendsto_nhds_unique reflected
  exact OriginalGamma.Source.WholePrimeLog.original_log_step_tendsto.congr'
    (Eventually.of_forall (fun N => by simp only [Function.comp_apply, LogD, log_reflect, seed_even]))

end
end OriginalGamma.Source.LogDifferencePa
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
