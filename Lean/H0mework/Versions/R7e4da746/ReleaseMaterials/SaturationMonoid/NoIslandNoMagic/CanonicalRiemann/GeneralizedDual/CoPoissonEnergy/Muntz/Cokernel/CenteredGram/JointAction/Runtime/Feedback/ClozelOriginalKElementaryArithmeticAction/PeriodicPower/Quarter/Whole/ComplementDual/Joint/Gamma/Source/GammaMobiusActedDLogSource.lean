import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaOrdinaryDPrincipalValueSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorStrongSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaMobiusActedDLog
open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace Topology BigOperators ArithmeticFunction
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.LogPairClosure
open OriginalGamma.Source.GammaOrdinaryDPrincipalValue
open OriginalGamma.Source.ConductorDual OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.JointLogConductor
noncomputable section
private theorem inverse_log_from_complete_source (v gamma logarithm : BurnolL2)
    (complete : GammaPair v gamma) (position : LogPair v logarithm) :
    LogPair (fourierL2.symm v) (fourierL2.symm (gamma-logarithm)) := by
  apply (ordinaryDPaid% log_pair_of_weak)
  intro test
  have full:=complete (𝓕 test)
  have first:=(dualStrongPaid% log_pair_pairing) _ _ _ _
    (original_log_schwartz_domain (𝓕 test)) position
  rw [wholeConductorTest,FourierTransform.fourierInv_fourier_eq,inner_add_left,first] at full
  calc
    _=inner ℂ (fourierL2 (logSchwartzL2 test)) v := (fourierL2.inner_map_eq_flip _ _).symm
    _=inner ℂ ((𝓕 test).toLp 2 volume) gamma-inner ℂ ((𝓕 test).toLp 2 volume) logarithm := by
      linear_combination full
    _=inner ℂ (test.toLp 2 volume) (fourierL2.symm (gamma-logarithm)) := by
      rw [←inner_sub_right,←SchwartzMap.toLp_fourier_eq]
      exact fourierL2.inner_map_eq_flip _ _

end
end OriginalGamma.Source.GammaMobiusActedDLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
