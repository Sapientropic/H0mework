import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PhysicalPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativePowerPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PhysicalPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Weighted
open scoped Topology InnerProductSpace
local notation "Hq"=>BurnolQuarterIntervalL2
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- Every original Jordan column is read on the same complete regular source, with its actual reverse-count field. -/
theorem actual_original_native_full_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    let observation:=burnolPaZeroObservation c zero
    let half:OriginalKCombCalculation.Half observation:=⟨c.rightHalf⟩
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
    inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo c)
      (CombSource.Division.rawIterate observation half.down m (wholeValue c zero h positive))=
      feedbackCoefficient observation half*
        burnolPaResolventSourceCoefficient c (OriginalKCombCofinalPaAction.E (wholeValue c zero h positive))+
      inner ℂ (sourceQ observation half) (wholeValue c zero h positive)+
      ∑ k∈Finset.range m,star (sourceCoefficient c m k)*
        inner ℂ (weightedCount (logBFirst c k:Hq))
          (burnolQuarterZeroExtension (normalizedRegular c zero)):=by
  dsimp only
  rw [actual_original_full_price c zero h positive]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [actual_weighted_native_price c zero (logBFirst c k:Hq)]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.NativePowerPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
