import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.FullResidual.Dynamics.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullResidualAction
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalFeedback
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFullSourceDynamics
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace Dyn
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
  (cofinal_collapsed_value cofinal_next_active cofinal_current_value cofinal_after_value cofinal_native_value)
end Dyn
namespace FR
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation
  (jointCode completeInput joint_complete)
end FR
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
  (collapseValue)
end CF
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (defaultFactory)
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (historyAt history_end_index actual_index complete_word)
end D
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace P
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
  (R code physicalProjection physicalRemainder observer)
end P
namespace C
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback (Value Var)
end C
namespace F
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFullResidualAction
  (factory initial firstCfg cofinalPacket cofinalInput original_runtime_whole original_root_future)
end F
local instance levelGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

theorem joint_complete_value (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    let generated := (FR.jointCode (P.code observation nontrivial half)).eval environment
    generated.1 + generated.2 =
      (P.physicalProjection ((P.R observation nontrivial half)
        ((FR.completeInput environment () ()).1 + (FR.completeInput environment () ()).2)),
       P.physicalRemainder ((P.R observation nontrivial half)
        ((FR.completeInput environment () ()).1 + (FR.completeInput environment () ()).2))) :=
  (FR.joint_complete (P.code observation nontrivial half) environment).trans rfl

variable (depth : Nat)
abbrev input (ordinal : Nat) := F.cofinalInput observation nontrivial half depth ordinal
def raw (ordinal : Nat) : BurnolL2 := (input observation nontrivial half depth ordinal).1 +
  (input observation nontrivial half depth ordinal).2

theorem next_pair (ordinal : Nat) : input observation nontrivial half depth (ordinal + 1) =
    (P.physicalProjection ((P.R observation nontrivial half) (raw observation nontrivial half depth ordinal)),
      P.physicalRemainder ((P.R observation nontrivial half) (raw observation nontrivial half depth ordinal))) :=
  (congrArg (fun row : (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2) => row.1 + row.2)
    (Dyn.cofinal_collapsed_value (W := PairValue C.Value) (X := C.Var)
      (F.initial observation nontrivial half depth) (F.firstCfg observation nontrivial half depth) (by rfl)
      (FR.jointCode (P.code observation nontrivial half)) (SF.defaultFactory (PairValue C.Value) C.Var ()) ordinal ())).trans
        (joint_complete_value observation nontrivial half _)

theorem raw_successor (ordinal : Nat) : raw observation nontrivial half depth (ordinal + 1) =
    (P.R observation nontrivial half) (raw observation nontrivial half depth ordinal) :=
  (congrArg (fun pair : BurnolL2 × BurnolL2 => pair.1 + pair.2)
    (next_pair observation nontrivial half depth ordinal)).trans
      (Submodule.starProjection_add_starProjection_orthogonal _)

theorem raw_source_iterate (ordinal : Nat) : raw observation nontrivial half depth ordinal =
    ((P.R observation nontrivial half).toLinearMap ^ ordinal) (raw observation nontrivial half depth 0) := by
  induction ordinal with
  | zero => rfl
  | succ ordinal previous =>
    exact (raw_successor observation nontrivial half depth ordinal).trans
      ((congrArg (P.R observation nontrivial half) previous).trans (by rw [pow_succ']; rfl))

theorem original_model_next (ordinal : Nat) :
    SourceGeneratedActionObservationHistory.modelAction
      (P.R observation nontrivial half).toLinearMap (P.observer observation half).toLinearMap
      (SourceGeneratedActionObservationHistory.projection
        (P.R observation nontrivial half).toLinearMap (P.observer observation half).toLinearMap
        (raw observation nontrivial half depth ordinal)) =
    SourceGeneratedActionObservationHistory.projection
      (P.R observation nontrivial half).toLinearMap (P.observer observation half).toLinearMap
      (raw observation nontrivial half depth (ordinal + 1)) :=
  (SourceGeneratedActionObservationHistory.modelAction_source
    (P.R observation nontrivial half).toLinearMap (P.observer observation half).toLinearMap
    (raw observation nontrivial half depth ordinal)).trans
      (congrArg (SourceGeneratedActionObservationHistory.projection
        (P.R observation nontrivial half).toLinearMap (P.observer observation half).toLinearMap)
        (raw_successor observation nontrivial half depth ordinal).symm)

theorem original_future_actual (ordinal : Nat) :
    P.observer observation half
      (((P.R observation nontrivial half).toLinearMap ^ ordinal)
        (SourceGeneratedActionObservationHistory.Hilbert.recover
          (P.R observation nontrivial half) (P.observer observation half)
          (SourceGeneratedActionObservationHistory.projection
            (P.R observation nontrivial half).toLinearMap (P.observer observation half).toLinearMap
            (raw observation nontrivial half depth 0)))) =
      P.observer observation half (raw observation nontrivial half depth ordinal) :=
  (SourceGeneratedActionObservationHistory.Hilbert.recover_complete_history
    (P.R observation nontrivial half) (P.observer observation half) (raw observation nontrivial half depth 0) ordinal).trans
      (congrArg (P.observer observation half) (raw_source_iterate observation nontrivial half depth ordinal).symm)

theorem full_history (ordinal : Nat) : type_of% (SF.D.history_end_index (F.factory observation nontrivial half)
    (F.initial observation nontrivial half depth) (F.firstCfg observation nontrivial half depth) (by rfl) (ordinal + 1)) :=
  SF.D.history_end_index _ _ _ _ _
theorem original_root_future (ordinal : Nat) (history : List PUnit.{1}) (target : Nat) : type_of%
    (F.original_root_future observation nontrivial half depth ordinal history target) :=
  F.original_root_future _ _ _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFullSourceDynamics
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
