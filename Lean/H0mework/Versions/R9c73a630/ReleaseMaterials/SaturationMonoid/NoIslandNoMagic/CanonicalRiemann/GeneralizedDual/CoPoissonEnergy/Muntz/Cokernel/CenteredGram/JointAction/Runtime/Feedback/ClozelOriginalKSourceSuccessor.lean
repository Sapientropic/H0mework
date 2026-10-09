import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConfiguredPairWriteback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombSourceSuccessor
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift RootInquiryCompletion CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace Q
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombConfiguredPairWriteback
  (sourceFrame sourceConfiguration writePair written_pair)
namespace C
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback (Value Var)
end C
namespace F
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombRegisteredSourceFeed (projected)
end F
namespace P
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction (R code physicalProjection physicalRemainder)
end P
end Q
namespace F
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (Factory Packet defaultFactory)
end F
namespace S
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
  (write oldPair nativeValue native_value born_environment nextCfg born successorPacket actual_compiles actual_whole actual_next full_frame second_decoder second_writeback cofinal)
end S
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeValue native_value)
end WB
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat)
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
attribute [local irreducible] Q.P.code
attribute [local instance] SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.levelGroups

def factory : F.Factory Q.C.Value Q.C.Var () := F.defaultFactory Q.C.Value Q.C.Var ()
def data : F.Packet (W := Q.C.Value) (X := Q.C.Var) (s := ()) 0 :=
  ⟨Q.sourceFrame observation nontrivial depth half,
   RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
     (Q.sourceFrame observation nontrivial depth half).registered.input.expression)⟩
abbrev configuration := Q.sourceConfiguration observation nontrivial half
abbrev nextConfiguration := S.nextCfg factory 0 (data observation nontrivial depth half)
  (configuration observation nontrivial half) (by rfl)
abbrev sourceBorn := S.born factory 0 (data observation nontrivial depth half)
  (configuration observation nontrivial half) (by rfl)
abbrev nextPacket := S.successorPacket factory 0 (data observation nontrivial depth half)
  (configuration observation nontrivial half) (by rfl)

theorem source_compiles : type_of% (S.actual_compiles factory 0 (data observation nontrivial depth half)
    (configuration observation nontrivial half) (by rfl)) := S.actual_compiles _ _ _ _ _
theorem source_whole : type_of% (S.actual_whole factory 0 (data observation nontrivial depth half)
    (configuration observation nontrivial half) (by rfl)) := S.actual_whole _ _ _ _ _
theorem source_next : type_of% (S.actual_next factory 0 (data observation nontrivial depth half)
    (configuration observation nontrivial half) (by rfl)) := S.actual_next _ _ _ _ _
theorem actual_full_frame : type_of% (S.full_frame factory 0 (data observation nontrivial depth half)
    (configuration observation nontrivial half) (by rfl)) := S.full_frame _ _ _ _ _
theorem actual_born_pair : (sourceBorn observation nontrivial depth half).activeEnvironment = (fun _ _ =>
      (Q.P.physicalProjection ((Q.P.R observation nontrivial half) (Q.F.projected observation nontrivial depth half)),
       Q.P.physicalRemainder ((Q.P.R observation nontrivial half) (Q.F.projected observation nontrivial depth half)))) := by
  have same : S.nativeValue factory 0 (data observation nontrivial depth half)
      (configuration observation nontrivial half) (by rfl) =
      WB.nativeValue (Q.sourceFrame observation nontrivial depth half)
        (Q.sourceConfiguration observation nontrivial half) (Q.writePair observation nontrivial half) :=
    (S.native_value factory 0 (data observation nontrivial depth half)
      (configuration observation nontrivial half) (by rfl)).trans
      (WB.native_value _ _ _).symm
  have oldSame : S.oldPair 0 (data observation nontrivial depth half)
      (configuration observation nontrivial half) =
      WB.oldPaid (Q.sourceFrame observation nontrivial depth half)
        (Q.sourceConfiguration observation nontrivial half) := by
    dsimp only [SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.oldPair, data, configuration,
      SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.L.Value,
      SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.L.groups,
      SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.levelGroups,
      SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.familyFactoryGroup]
  let updated : BurnolL2 × BurnolL2 := S.oldPair 0 (data observation nontrivial depth half)
    (configuration observation nontrivial half) + S.nativeValue factory 0 (data observation nontrivial depth half)
      (configuration observation nontrivial half) (by rfl)
  have total : updated =
      (Q.P.physicalProjection ((Q.P.R observation nontrivial half) (Q.F.projected observation nontrivial depth half)),
       Q.P.physicalRemainder ((Q.P.R observation nontrivial half) (Q.F.projected observation nontrivial depth half))) :=
    (congrArg₂ (fun left right : BurnolL2 × BurnolL2 => left + right) oldSame same).trans
      (Q.written_pair observation nontrivial depth half)
  have active : (sourceBorn observation nontrivial depth half).activeEnvironment =
      S.write 0 (configuration observation nontrivial half) updated :=
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
    (S.born_environment factory 0 (data observation nontrivial depth half)
      (configuration observation nontrivial half) (by rfl))
  have writer : S.write 0 (configuration observation nontrivial half) updated = (fun _ _ => updated) := by
    funext target coordinate
    cases target
    rfl
  exact active.trans (writer.trans
    (congrArg (fun value : BurnolL2 × BurnolL2 => fun _target _coordinate => value) total))

theorem next_source_decoder : type_of% (S.second_decoder factory 0 (data observation nontrivial depth half)
    (configuration observation nontrivial half) (by rfl)) := S.second_decoder _ _ _ _ _
theorem next_source_writeback : type_of% (@S.second_writeback _ _ _ factory 0
    (data observation nontrivial depth half) (configuration observation nontrivial half) (by rfl)) :=
  @S.second_writeback _ _ _ factory 0 (data observation nontrivial depth half)
    (configuration observation nontrivial half) (by rfl)
def sourceCofinal (bound : Nat) := S.cofinal factory 0 (data observation nontrivial depth half)
  (configuration observation nontrivial half) (by rfl) bound
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombSourceSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
