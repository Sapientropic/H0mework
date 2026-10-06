import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Carried

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (count : Nat)

theorem actual_target : (frame root visit recognition U7 calculus count).currentState =
    SourceGeneratedInquiryReceiptAction.targetState
      (sourceFrame root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus) := rfl
theorem actual_current : (runtime root visit recognition U7 calculus count).initialState.engine.node.erase =
    (SourceGeneratedInquiryReceiptAction.targetPresentation
      (sourceFrame root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus)).erase :=
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.actual_current
    (frame root visit recognition U7 calculus count) 0
theorem actual_source : (actualGenerated root visit recognition U7 calculus count).1 =
    Receipt.generated root visit recognition U7 calculus count := rfl
theorem actual_input : (frame root visit recognition U7 calculus count).rawRead.expression =
    (Receipt.registered root visit recognition U7 calculus count).input.expression := rfl
theorem actual_environment : (frame root visit recognition U7 calculus count).rawRead.environment =
    SourceGeneratedInquiryReceiptAction.afterEnvironment
      (sourceFrame root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus) :=
  (frame root visit recognition U7 calculus count).raw_environment.trans
    (SourceGeneratedInquiryReceiptAction.actual_updated_environment _ _)
theorem generated_successor : type_of% (SourceGeneratedInquiryReceiptAction.successor_valid
    (sourceFrame root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus)) :=
  SourceGeneratedInquiryReceiptAction.successor_valid _ _
theorem literal_target_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next
    (sourceFrame root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus)) :=
  SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem old_projection (projection : (SourceGeneratedInquiryReceiptAction.old
    (sourceFrame root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus)).root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    type_of% (SourceGeneratedInquiryReceiptAction.all_old_projection
      (sourceFrame root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus) projection) :=
  SourceGeneratedInquiryReceiptAction.all_old_projection _ _ projection
theorem canonical_next (stage : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next_preserves
      (frame root visit recognition U7 calculus count) stage) :=
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next_preserves _ stage
theorem actual_next (stage : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next
      (frame root visit recognition U7 calculus count) stage) :=
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.macro_next _ stage
theorem no_refill : type_of%
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.no_refill
      (frame root visit recognition U7 calculus count)) :=
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.no_refill _
theorem noetherian : type_of%
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.continuation_wellFounded
      (frame root visit recognition U7 calculus count)) :=
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment.continuation_wellFounded _

private theorem trace_map {X Y : Type u} (f : X → Y) (tree : RootedAccountedUnfolding X) :
    (tree.map f).trace = tree.trace.map f :=
  RootedAccountedUnfolding.rec
    (motive_1:=fun current => (current.map f).trace=current.trace.map f)
    (motive_2:=fun branches => RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.mapBranches f branches)=
      (RootedAccountedUnfolding.traceBranches branches).map f)
    (fun datum branches previous => by
      simp only [RootedAccountedUnfolding.map,RootedAccountedUnfolding.trace,List.map_cons]
      exact congrArg (List.cons (f datum)) previous)
    (by simp only [RootedAccountedUnfolding.mapBranches,RootedAccountedUnfolding.traceBranches,List.map_nil])
    (fun head tail headProof tailProof => by
      simp only [RootedAccountedUnfolding.mapBranches,RootedAccountedUnfolding.traceBranches,List.map_append]
      exact AccountedList.congrArgTwo List.append headProof tailProof) tree

theorem physical_preserved (event) (present : event ∈ (physicalInventory root visit recognition U7 calculus count).trace) :
    migration root visit recognition U7 calculus count event ∈ (stock root visit recognition U7 calculus count).trace := by
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  rw [trace_map]
  exact List.mem_map.mpr ⟨event, present, rfl⟩
theorem paid_trace_preserved (event) (present : event ∈ (paidExposure root visit recognition U7 calculus count).trace) :
    event ∈ (stock root visit recognition U7 calculus count).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem scalar_stock_preserved (old : RootedAccountedUnfolding (PresentedRelationEventAt
    (Expr (JointQuery.Value root visit recognition) (JointQuery.Variable root visit recognition) .result)))
    (carried : (sourceFrame root visit recognition U7 calculus count).inventory = some old)
    (event) (present : event ∈ old.trace) :
    migration root visit recognition U7 calculus count
      (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent event) ∈
        (stock root visit recognition U7 calculus count).trace :=
  physical_preserved root visit recognition U7 calculus count _
    (SourceGeneratedInquiryReceiptAction.Inventory.Carried.input_carried_written _ old carried event present)
theorem pair_stock_preserved (old : RootedAccountedUnfolding (PresentedRelationEventAt
    (Expr (PairValue (JointQuery.Value root visit recognition)) (JointQuery.Variable root visit recognition) .result)))
    (carried : (sourceFrame root visit recognition U7 calculus count).pairInventory = some old)
    (event) (present : event ∈ old.trace) :
    migration root visit recognition U7 calculus count event ∈ (stock root visit recognition U7 calculus count).trace := by
  apply physical_preserved root visit recognition U7 calculus count
  apply SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.complete_written_preserves
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.priorPairInventory
  dsimp only [SourceOperationInquiry.Context.Faces.Execution.Activation.epoch]
  rw [carried]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
