import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalPaAction.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalStrongAction
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

namespace D
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSourceDynamics
  (factory initial firstCfg packet input raw raw_xi_source raw_successor next_pair full_history original_runtime_whole original_root_future)
end D
namespace P
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction (R)
end P
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalRAction
  (parameter_rightQuarter original_R_direct actual_source_gap)
end Paid
namespace AD
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (index actual_index)
end AD
namespace RC
export ActualCofinalRootResidualConsumer
  (original_compiles original_whole actual_generated_current rooted_material_source actual_root_eliminate)
end RC

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def actualSourceTick (ordinal : Nat) : Nat :=
  AD.index (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
    (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1)

theorem actual_source_packet_index (ordinal : Nat) : type_of%
    (AD.actual_index (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
      (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1)) :=
  AD.actual_index _ _ _ _ _

theorem actual_source_whole (ordinal : Nat) : type_of%
    (D.original_runtime_whole observation nontrivial half depth (actualSourceTick observation nontrivial half depth ordinal)) :=
  D.original_runtime_whole _ _ _ _ _

theorem actual_source_boundary (ordinal : Nat) (shift : ℝ) :
    burnolMultiplicativeDilation (-shift / 2) (D.raw observation nontrivial half depth (ordinal + 1)) -
      positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift •
        D.raw observation nontrivial half depth (ordinal + 1) =
    positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift •
      burnolDirectRightResolventSignedBoundary (observation.coordinate / 2)
        (D.raw observation nontrivial half depth ordinal) shift := by
  rw [D.raw_successor, Paid.original_R_direct]
  exact burnolDirectRightResolvent_sourceBoundary (observation.coordinate / 2)
    (Paid.parameter_rightQuarter observation half) _ shift

theorem actual_source_strong (ordinal : Nat) :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation (-shift / 2)
      (D.raw observation nontrivial half depth (ordinal + 1)))
      ((observation.coordinate / 2 - 1 / 4) • D.raw observation nontrivial half depth (ordinal + 1) +
        D.raw observation nontrivial half depth ordinal) 0 := by
  rw [D.raw_successor, Paid.original_R_direct]
  exact burnolDirectRightResolventOrbit_hasDerivAt (observation.coordinate / 2)
    (Paid.parameter_rightQuarter observation half) _

-- This read uses the complete orbit, including the common-gap residual.
def sourceRecover (value : BurnolL2) : BurnolL2 :=
  deriv (fun shift : ℝ => burnolMultiplicativeDilation (-shift / 2) value) 0 -
    (observation.coordinate / 2 - 1 / 4) • value

theorem actual_source_recovery (ordinal : Nat) :
    sourceRecover observation (D.raw observation nontrivial half depth (ordinal + 1)) =
      D.raw observation nontrivial half depth ordinal := by
  unfold sourceRecover
  rw [(actual_source_strong observation nontrivial half depth ordinal).deriv]
  module

theorem actual_source_backward (ordinal steps : Nat) :
    (sourceRecover observation)^[steps] (D.raw observation nontrivial half depth (ordinal + steps)) =
      D.raw observation nontrivial half depth ordinal := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    rw [Function.iterate_succ_apply]
    rw [show ordinal + (steps + 1) = (ordinal + steps) + 1 by omega,
      actual_source_recovery]
    exact previous

theorem actual_pair_source_recovery (ordinal : Nat) :
    sourceRecover observation ((D.input observation nontrivial half depth (ordinal + 1)).1 +
      (D.input observation nontrivial half depth (ordinal + 1)).2) =
    (D.input observation nontrivial half depth ordinal).1 +
      (D.input observation nontrivial half depth ordinal).2 :=
  actual_source_recovery observation nontrivial half depth ordinal

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalStrongAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
