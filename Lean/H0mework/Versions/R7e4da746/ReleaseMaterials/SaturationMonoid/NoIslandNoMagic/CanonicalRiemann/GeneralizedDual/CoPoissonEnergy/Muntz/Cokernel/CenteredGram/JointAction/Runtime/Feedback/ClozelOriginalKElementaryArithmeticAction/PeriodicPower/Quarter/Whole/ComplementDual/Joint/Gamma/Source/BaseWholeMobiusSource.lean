import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.ConductorDualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FirstStateSynthesis
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.Isometry
import H0mework.Arithmetic.SonineProjection.MeanZeroBlock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCounting
import H0mework.Versions.R7e4da746.Arithmetic.RieszCanonicalRaw.RieszSingleFourierSource
import H0mework.Arithmetic.MellinProjection.TailKernel
import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.BaseWholeMobius
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace ArithmeticFunction BigOperators
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszSource OriginalRieszSourceGreen
open OriginalGamma.Source.CountingQuadraticLimit
open OriginalGamma.Source.FirstStateSynthesis OriginalGamma.Source.KappaConductor
noncomputable section
local notation "T" => burnolTateReciprocalL2

macro "baseStatePaid% " field:ident : term => do
  let owner := Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FirstStateSynthesis 0
  let scope := `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.FirstStateSynthesis
  return Lean.mkIdent (owner.append (scope.append field.getId))

private theorem original_b_first :
    ∀ c : BurnolCompletedMellinCoordinate, originalBSynthesis c ConstantDual.value = CountingDual.value c := by
  intro c
  have strong := ((originalBSynthesis c).continuous.tendsto ConstantDual.value).comp ConstantDual.original_tendsto
  have generated := CountingDual.original_dual_tendsto c
  rw [original_b_synthesis] at generated
  have finite (N : ℕ) : DualSource.source N (originalBSynthesis c ConstantDual.seed) =
      originalBSynthesis c (DualSource.source N ConstantDual.seed) := by
    simpa only [← CountingDual.dual_eq_adjoint] using
      (baseStatePaid% b_commute) c (CountingDual.sourceCLM N).adjoint
        (fun h v => by simpa only [← CountingDual.dual_eq_adjoint] using dual_dilation N h v) ConstantDual.seed
  exact tendsto_nhds_unique strong (generated.congr' (Eventually.of_forall finite))

theorem original_base_first_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    originalBaseSynthesis c ConstantDual.value = -PositionCounting.value c zero := by
  have source := original_dual_synthesis c zero
  rw [original_b_first] at source
  simp only [originalDualField, originalFirstField, map_neg, map_sub,
    burnolTateReciprocalL2_involutive] at source
  have paired : T (originalBaseSynthesis c ConstantDual.value) = -T (PositionCounting.value c zero) := by
    exact sub_left_inj.mp source.symm
  have actual := congrArg T paired
  simpa only [map_neg, burnolTateReciprocalL2_involutive] using actual

end
end OriginalGamma.Source.BaseWholeMobius
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
