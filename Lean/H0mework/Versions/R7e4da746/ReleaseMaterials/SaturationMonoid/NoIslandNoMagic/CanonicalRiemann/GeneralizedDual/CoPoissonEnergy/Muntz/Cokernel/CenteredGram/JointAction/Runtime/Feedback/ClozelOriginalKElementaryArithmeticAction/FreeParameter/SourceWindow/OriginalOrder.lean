import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.TopRead
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.OriginalOrder
open Complex Filter MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerSource OriginalUnitMellinSource.Band OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open OriginalUnitXiConjugateOrderSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem coordinate_eq {a b : BurnolCompletedMellinCoordinate} (same : a.value=b.value) : a=b := by
  cases a
  cases b
  cases same
  rfl

def conjugateHalf (observation : GeneratedRiemannZeroObservation)
    (half : OriginalKCombCalculation.Half observation) :
    OriginalKCombCalculation.Half (conjugateZeroObservation observation) := ⟨by
  change 1/2 < (starRingEnd ℂ observation.coordinate).re
  simpa only [conj_re] using half.down⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "reflected" => conjugateZeroObservation observation
local notation "reflectedHalf" => conjugateHalf observation half
local notation "test" h => OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest c h
include nontrivial

/-- The original owner's original m is consumed on the actual conjugate Unit, at the fixed test. -/
theorem actual_original_order_top_pair (h : ℝ) (nonnegative : 0≤h)
    (bounded : q*Real.exp h<2*q) :
    inner ℂ (test h) (((burnolDirectRightResolventCLM (barC c))^m)
      (burnolUnitTailResponse (barC c) 4))=
      bandMean (barC c) m*inner ℂ (burnolQuarterRestriction (fourierL2 (test h))) (intervalConstant q)+
      (-2*burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner reflected)*
        inner ℂ (burnolQuarterRestriction (fourierL2 (test h))) (SingularCounting.powerL2 c)+
      fullTopBandPrice reflected reflectedHalf (test h) h := by
  have same : burnolDivisionZeroCompletedMellinCoordinate reflected (reflectedHalf).down=barC c := by
    apply coordinate_eq
    rfl
  have twice : barC (barC c)=c := by
    apply coordinate_eq
    exact star_star _
  have order := actual_original_Xi_order_conjugate c
  change generatedRiemannXiZeroOrder ActualAnalyticOwner (reflected).coordinate=m at order
  have source := actual_radius_top_pair reflected (observation.conjugate_nontrivial nontrivial)
    reflectedHalf c h nonnegative bounded
  change inner ℂ (test h)
    (((burnolDirectRightResolventCLM (burnolDivisionZeroCompletedMellinCoordinate reflected (reflectedHalf).down))^
      (generatedRiemannXiZeroOrder ActualAnalyticOwner (reflected).coordinate))
      (burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate reflected (reflectedHalf).down) 4))=_ at source
  rw [order,same,twice] at source
  exact source

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.OriginalOrder
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
