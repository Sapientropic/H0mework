import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaForwardCountPhiSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
import H0mework.Arithmetic.BurnolCarrier.AdditiveFullEvenL2
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier
import H0mework.Arithmetic.BurnolPhysical.PhysicalityProjection
import H0mework.Arithmetic.BurnolMellin.CompletedMellinEvaluatorKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCounting
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Arithmetic.TruncatedFourier.SonineSolve

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaForwardCountKPrice
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.GammaForwardCountPhi
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.ConductorDual
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.CountingQuadraticLimit
open OriginalGamma.Source.KappaConductor OriginalGamma.Source.PhiConductorReadback
open OriginalGamma.Source.GammaMobiusActedDLog
macro "programmeIndependentLogPaid% " field:ident : term => do
  let owner:=Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaMobiusActedDLogSource 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.GammaMobiusActedDLog
  return Lean.mkIdent (owner.append (scope.append field.getId))
noncomputable section
local notation "K" => burnolCompletedMellinRieszVector
local notation "A" => CountingDual.sourceCLM
local notation "D" => DualSource.source
local notation "F" => fourierL2

private def forwardGammaPositionLog (c : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  D N (actualKernelFrequencyLog c)-LogD N (F (K c:BurnolL2))
private def forwardGammaFrequencyLog (c : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  fourierL2.symm (F (A N (actualGammaKernel c))-forwardGammaPositionLog c N)

private theorem actual_forward_gamma_position_log_source (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    LogPair (F (A N (K c:BurnolL2))) (forwardGammaPositionLog c N) := by
  have frequency:=(actual_kernel_complete_log_sources c).2
  have even:=mem_evenL2ClosedFace_iff.mp (K c).property.2
  have same : fourierL2.symm (K c:BurnolL2)=F (K c:BurnolL2) := by
    rw [fourierL2_symm_eq_reflect_fourierL2,←fourierL2_reflectL2_commute,even]
  rw [same] at frequency
  have generated:=original_finite_log_domain 1 N _ _ frequency
  rw [CountingDual.sourceCLM_apply,←KCounting.dual_fourier N (K c:BurnolL2)]
  simpa only [forwardGammaPositionLog,LogD,logCountingCLM_apply,original_reverse_source,
    ←CountingDual.dual_eq_adjoint,Complex.ofReal_one,one_smul] using generated

private theorem actual_forward_gamma_frequency_log_source (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    LogPair (fourierL2.symm (F (A N (K c:BurnolL2)))) (forwardGammaFrequencyLog c N) := by
  have full:=(programmeGammaFourierPaid% gamma_pair_fourier) _ _
    (actual_original_forward_gamma_kernel_count_source c N)
  exact (programmeIndependentLogPaid% inverse_log_from_complete_source) _ _ _ full
    (actual_forward_gamma_position_log_source c N)

end
end OriginalGamma.Source.GammaForwardCountKPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
