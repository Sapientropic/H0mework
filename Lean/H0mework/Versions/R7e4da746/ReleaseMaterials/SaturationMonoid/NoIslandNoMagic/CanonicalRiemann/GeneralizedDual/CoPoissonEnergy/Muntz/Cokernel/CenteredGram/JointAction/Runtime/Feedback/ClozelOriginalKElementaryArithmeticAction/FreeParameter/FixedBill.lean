import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedEvaluator
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.FixedBill
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource.ResponseForcing.Source
open scoped InnerProductSpace Topology
local notation "K" => burnolCompletedMellinRieszVector

/-- The finite-h original price consumes the actual first counted P and b, with both moved tests intact. -/
theorem actual_fixed_bill (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
 (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) :
 responseFinitePrice c h=
  inner ℂ (PositionCounting.value c zero) (burnolMultiplicativeDilation h (K c:BurnolL2))-
   (Real.exp (h/2):ℂ)*inner ℂ (PositionCounting.value c zero) (K c:BurnolL2)+
  inner ℂ (CountingDual.value c) (burnolMultiplicativeDilation h (fourierL2 (K c:BurnolL2)))-
   (Real.exp (h/2):ℂ)*inner ℂ (CountingDual.value c) (fourierL2 (K c:BurnolL2)) := by
 rw [←actual_finite_price,←OriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice.source_pair_finite_price c h nonnegative]
 exact CountedEvaluator.source_pair c zero h nonnegative bounded

end OriginalKElementaryArithmeticAction.FreeParameter.FixedBill
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
