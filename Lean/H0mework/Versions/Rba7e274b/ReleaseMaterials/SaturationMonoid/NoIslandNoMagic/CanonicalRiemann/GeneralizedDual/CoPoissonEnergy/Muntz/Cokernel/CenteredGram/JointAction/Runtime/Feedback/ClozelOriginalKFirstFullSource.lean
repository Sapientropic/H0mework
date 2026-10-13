import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceDynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceSuccessor
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace P
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
  (initial value R code result result_value complete_raw physicalProjection physicalRemainder)
end P
namespace C
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback
  (Value Var material endpointOccurrence initial_environment constantEnvironment)
end C
namespace F
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombRegisteredSourceFeed
  (configuration action_raw action_value material_raw material_trace)
end F
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence next)
end S
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active epoch mathNext)
end E
namespace R
export SourceGeneratedInquiryReceiptAction (actionResultAt actualMaterial afterEnvironment)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input budget)
end N
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (Factory Packet Seed defaultFactory)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
  (born selected nextCfg successorPacket actual_writeback write actual_compiles actual_whole actual_next receiver_inventories born_inventories)
end SS
local instance levelGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value C.Value grade target) :=
  L.groups C.Value grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

abbrev initial := P.initial observation nontrivial depth half
abbrev configuration := F.configuration observation nontrivial half

theorem initial_paid : S.next (initial observation nontrivial half depth) (configuration observation nontrivial half) =
    (initial observation nontrivial half depth).mathNext := by
  unfold S.next
  cases actual : (initial observation nontrivial half depth).action with
  | inr paid => rfl
  | inl settled =>
    have zero := (RootGeneratedDebtActivationJointSource.Idle.law
      (initial observation nontrivial half depth).registered.input.environment
      (initial observation nontrivial half depth).registered.input.expression).settlement_budget_zero settled
    have clock := SourceRegisteredClaimClock.remainder_generated (initial observation nontrivial half depth)
    have cost := N.budget (C.material observation nontrivial depth half (C.endpointOccurrence observation nontrivial depth half))
    change remaining (initial observation nontrivial half depth).event.state.1 = 0 at zero
    change remaining (initial observation nontrivial half depth).event.state.1 =
      remaining (initial observation nontrivial half depth).registered.input.expression - (0 + 1) at clock
    change remaining (initial observation nontrivial half depth).registered.input.expression = _ at cost
    omega

theorem updated_environment :
    (N.input (R.actualMaterial (initial observation nontrivial half depth) (configuration observation nontrivial half))).environment =
      (fun _ _ => (P.value observation nontrivial depth half, (0 : BurnolL2))) := by
  have after : R.afterEnvironment (initial observation nontrivial half depth) (configuration observation nontrivial half) =
      (fun _ _ => (P.value observation nontrivial depth half, (0 : BurnolL2))) := by
    unfold R.afterEnvironment
    rw [initial_paid, F.action_raw]
    unfold NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction.raw
    have same := E.epoch (E.mathNext (C.initial_environment observation nontrivial depth half))
    rw [same]
    rfl
  exact (add_sub_cancel (R.actualMaterial (initial observation nontrivial half depth) (configuration observation nontrivial half)).environment
    (R.afterEnvironment (initial observation nontrivial half depth) (configuration observation nontrivial half))).trans after

def split : BurnolL2 × BurnolL2 :=
  (P.physicalProjection ((P.R observation nontrivial half) (P.value observation nontrivial depth half)),
   P.physicalRemainder ((P.R observation nontrivial half) (P.value observation nontrivial depth half)))

theorem updated_value :
    (R.actualMaterial (initial observation nontrivial half depth) (configuration observation nontrivial half)).raw.eval
      (N.input (R.actualMaterial (initial observation nontrivial half depth) (configuration observation nontrivial half))).environment =
        split observation nontrivial half depth := by
  rw [F.material_raw, updated_environment]
  rfl

theorem original_receipt_identity :
    (R.actionResultAt (initial observation nontrivial half depth) (configuration observation nontrivial half)
      (S.actualOccurrence (initial observation nontrivial half depth))).2.2.1 =
        (P.result observation nontrivial half (initial observation nontrivial half depth)).2.2.1 :=
  (F.action_value observation nontrivial half _).trans (P.result_value observation nontrivial half _).symm

theorem original_source_trace :
    (R.actualMaterial (initial observation nontrivial half depth) (configuration observation nontrivial half)).state.2.length = 3 :=
  F.material_trace observation nontrivial half _

def factory : SF.Factory C.Value C.Var () := SF.defaultFactory C.Value C.Var ()
def data : SF.Packet (W := C.Value) (X := C.Var) (s := ()) 0 :=
  ⟨initial observation nontrivial half depth,
   RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
     (initial observation nontrivial half depth).registered.input.expression)⟩
abbrev born : A.M.Frame (Value := PairValue C.Value) (Var := C.Var) (sort := ()) :=
  SS.born factory 0 (data observation nontrivial half depth) (configuration observation nontrivial half) (by rfl)
abbrev nextPacket := SS.successorPacket factory 0 (data observation nontrivial half depth)
  (configuration observation nontrivial half) (by rfl)
abbrev nextCfg := SS.nextCfg factory 0 (data observation nontrivial half depth)
  (configuration observation nontrivial half) (by rfl)

theorem actual_born_pair : (born observation nontrivial half depth).activeEnvironment =
    (fun _ _ => split observation nontrivial half depth) := by
  have written := E.active (SS.actual_writeback factory 0 (data observation nontrivial half depth)
    (configuration observation nontrivial half) (by rfl))
  have writer : SS.write 0 (configuration observation nontrivial half)
      ((R.actualMaterial (initial observation nontrivial half depth) (configuration observation nontrivial half)).raw.eval
        (N.input (R.actualMaterial (initial observation nontrivial half depth) (configuration observation nontrivial half))).environment) =
      (fun _ _ => split observation nontrivial half depth) := by
    funext target name
    cases target
    exact updated_value observation nontrivial half depth
  exact written.trans writer

theorem actual_complete : ((born observation nontrivial half depth).activeEnvironment () ()).1 +
    ((born observation nontrivial half depth).activeEnvironment () ()).2 =
      (P.R observation nontrivial half) (P.value observation nontrivial depth half) := by
  rw [actual_born_pair]
  exact Submodule.starProjection_add_starProjection_orthogonal _

theorem actual_whole : type_of% (SS.actual_whole factory 0 (data observation nontrivial half depth)
    (configuration observation nontrivial half) (by rfl)) := SS.actual_whole _ _ _ _ _
theorem actual_next : type_of% (SS.actual_next factory 0 (data observation nontrivial half depth)
    (configuration observation nontrivial half) (by rfl)) := SS.actual_next _ _ _ _ _
theorem all_inventories : type_of% (SS.born_inventories factory 0 (data observation nontrivial half depth)
    (configuration observation nontrivial half) (by rfl)) := SS.born_inventories _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
