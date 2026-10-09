import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
namespace R
export SourceGeneratedInquiryReceiptAction (old birthProgram sourceEvent)
end R
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (targetCoface optionalTargetCoface epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (datum root visit queryLaw resultLaw consumerLaw compilationLaw)
end Shared
end A
namespace Owned
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.RootOwned
 (sourceFrame sourceProgramme sourceInitial sourceSeed configuration runtime)
end Owned
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (anchor sourceStage stage : Nat)
namespace Lower
variable {S : Type u} {Value Var : S → Type u} [∀ s, AddCommGroup (Value s)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=s))
variable (programme : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=SourceOperationScalarInventoryLift.PairValue Value) (PhysicalVar:=cfg.LowVar) (sort:=s))
theorem target_root (event : SourceGeneratedInquiryReceiptAction.Configured.Event frame cfg) :
 (targetAt frame cfg programme event).targetRoot = A.Shared.root
 (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg) programme := rfl
theorem target_next (event : SourceGeneratedInquiryReceiptAction.Configured.Event frame cfg) :
 (targetAt frame cfg programme event).targetAnswerAndNext.nextCurrent =
 ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
  (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg).registered
  (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg).packetAt,
  (A.Shared.root (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg) programme).toAuthoritativeRoot,
  A.Shared.visit (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg) programme⟩ := by
 change (A.Shared.root (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg) programme).generatedNextCurrentAt
  (.finite (A.Shared.root (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg) programme).toAuthoritativeRoot.toRoot.initialVisit) = _
 apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
 rfl
theorem old_outcome (event : SourceGeneratedInquiryReceiptAction.Configured.Event frame cfg)
 (projection : (R.old frame cfg).root.toAuthoritativeRoot.source.projectionLaw.Projection) :
 type_of% ((targetAt frame cfg programme event).oldOutcome_heq projection) :=
 (targetAt frame cfg programme event).oldOutcome_heq projection
theorem compiles : (state frame cfg programme).compileInquiry
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame cfg) =
 .debtAdmission (generatedAction frame cfg programme) := rfl
theorem successor_valid : (targetPresentation frame cfg programme).erase =
 (RootInquiryProcessNode.answered (sourcePresentation frame cfg programme)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame cfg)).erase ∧
 (RootInquiryProcessNode.active (sourcePresentation frame cfg programme)).PreservesGeneratedLivingLawAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame cfg)
  (.active (targetPresentation frame cfg programme)) := by
 apply RootInquiryProcessNode.active_debtAdmission_successor_valid
  (sourcePresentation frame cfg programme) (targetPresentation frame cfg programme)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame cfg)
  (generatedAction frame cfg programme) (compiles frame cfg programme)
 · exact (congrArg (fun current =>
    (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World
      (SourceGeneratedInquiryReceiptAction.Configured.lowInitial frame cfg).registered,current⟩ :
      AnyAuthoritativeRootCurrent.{u}))
    (target_next frame cfg programme (R.sourceEvent frame cfg))).symm
 · exact HEq.rfl
end Lower
theorem actual_target_root (event) : type_of% (Lower.target_root
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage) event) := Lower.target_root _ _ _ event
theorem actual_target_next (event) : type_of% (Lower.target_next
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage) event) := Lower.target_next _ _ _ event
theorem actual_old_outcome (event) (projection) : type_of% (Lower.old_outcome
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage) event projection) := Lower.old_outcome _ _ _ event projection
theorem actual_compiles : type_of% (Lower.compiles
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage)) := Lower.compiles _ _ _
theorem actual_successor_valid : type_of% (Lower.successor_valid
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (receiverProgramme root visit rec U7 calculus anchor sourceStage stage)) := Lower.successor_valid _ _ _
theorem target_initial : (Owned.runtime root visit rec U7 calculus anchor sourceStage stage).initialState.engine.node =
 .active (targetPresentation root visit rec U7 calculus anchor sourceStage stage) := rfl
theorem source_root : (state root visit rec U7 calculus anchor sourceStage stage).root=
 (R.old (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (sourceProgramme root visit rec U7 calculus anchor sourceStage)).root := rfl
theorem source_visit : (state root visit rec U7 calculus anchor sourceStage stage).visit=
 (R.old (sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (sourceProgramme root visit rec U7 calculus anchor sourceStage)).visit := rfl
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
