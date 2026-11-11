import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaKernelWholeWeakCountSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KForwardWholeSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Arithmetic.BurnolCarrier.AdditiveFullEvenL2
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.BurnolPhysical.PhysicalityProjection
import H0mework.Arithmetic.BurnolMellin.CompletedMellinEvaluatorKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Arithmetic.MellinProjection.TailKernel

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaUnitFourierClockKPrice
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.GammaKernelWholeWeakCount OriginalGamma.Source.KGamma
open OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.ConductorDual
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.RelativeConductorStrong
open OriginalGamma.Source.JointLogConductor OriginalGamma.Source.FirstConductor
open OriginalGamma.Source.KForwardWhole OriginalGamma.Source.CountingQuadraticLimit
open OriginalGamma.Source.KappaConductor
noncomputable section
local notation "q" => (1/4:ℝ)
local notation "F" => fourierL2
local notation "RieszK" => burnolCompletedMellinRieszVector

private def countedKernelPositionLog (c : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 :=
  DualSource.source N (actualKernelPositionLog c)-logProgramme 1 N (RieszK c:BurnolL2)
private theorem counted_kernel_position_source (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    LogPair (DualSource.source N (RieszK c:BurnolL2)) (countedKernelPositionLog c N) := by
  have source:=original_finite_log_domain 1 N (RieszK c:BurnolL2) (actualKernelPositionLog c)
    (actual_kernel_complete_log_sources c).1
  rw [original_reverse_source,original_reverse_source,←CountingDual.dual_eq_adjoint,
    ←CountingDual.dual_eq_adjoint] at source
  simpa only [Complex.ofReal_one,one_smul,countedKernelPositionLog] using source

end
end OriginalGamma.Source.GammaUnitFourierClockKPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
