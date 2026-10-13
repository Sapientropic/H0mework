import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKAmbientPricing
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFirstFullSourceDynamics
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalRAction
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace D
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSourceDynamics (raw input raw_xi_source raw_successor next_pair original_runtime_whole original_root_future)
end D
namespace P
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction (R)
end P
namespace Pricing
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Pricing (ambient_R_positionGap ambient_R_scalar_action)
end Pricing
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

include half in
theorem parameter_rightQuarter : 1/4 < (observation.coordinate/2).re := by
 rw [Complex.div_re]
 norm_num
 linarith [half.down]

theorem original_R_direct (value : BurnolL2) : P.R observation nontrivial half value =
 burnolDirectRightResolvent (observation.coordinate/2) value := rfl

private theorem original_R_iterate_gap (steps : Nat) :
 ((P.R observation nontrivial half).toLinearMap ^ steps) (burnolPaCombApproximation 0 : BurnolL2) ∈
 locallyConstantFace burnolUnscaledCommonGapRadius := by
 induction steps with
 | zero => exact (burnolPaCombApproximation 0).property.1.1
 | succ steps previous =>
  rw [pow_succ', Module.End.mul_apply]
  change P.R observation nontrivial half _ ∈ _
  rw [original_R_direct]
  exact Pricing.ambient_R_positionGap (observation.coordinate/2) (parameter_rightQuarter observation half) _ previous

theorem actual_source_gap (ordinal : Nat) : D.raw observation nontrivial half depth ordinal ∈
 locallyConstantFace burnolUnscaledCommonGapRadius := by
 rw [D.raw_xi_source]
 exact original_R_iterate_gap observation nontrivial half _

theorem actual_source_scalar_action (ordinal : Nat) (w : ℂ) (wRight : 1/4 < w.re) (wBelow : w.re < 1/2) :
 burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
  (D.raw observation nontrivial half depth (ordinal+1)) =
 (-(1/(observation.coordinate/2+w-(1/2 : ℂ)))) *
 burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
  (D.raw observation nontrivial half depth ordinal) := by
 rw [D.raw_successor, original_R_direct]
 exact Pricing.ambient_R_scalar_action (observation.coordinate/2) (parameter_rightQuarter observation half)
  _ (actual_source_gap observation nontrivial half depth ordinal) w wRight wBelow

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
