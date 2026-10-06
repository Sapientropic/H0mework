import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Action.Source
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (frame : Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : C.Occurrence frame (current:=current))

theorem actual_equation_at : (rawAt root visit recognition frame occurrence).expression.eval
    (rawAt root visit recognition frame occurrence).environment =
      (Inventory.expression root visit recognition).eval (generatedEnvironmentAt root visit recognition frame occurrence) :=
  Expr.eval_subst _ _ _
theorem environment_update_at : environmentAt root visit recognition frame occurrence +
    incrementAt root visit recognition frame occurrence = generatedEnvironmentAt root visit recognition frame occurrence :=
  add_sub_cancel _ _
theorem actual_update_at : (rawAt root visit recognition frame occurrence).expression.eval
    (rawAt root visit recognition frame occurrence).environment =
      (Inventory.expression root visit recognition).eval (environmentAt root visit recognition frame occurrence) +
        (Inventory.expression root visit recognition).effect (environmentAt root visit recognition frame occurrence)
          (incrementAt root visit recognition frame occurrence) :=
  (actual_equation_at root visit recognition frame occurrence).trans
    ((congrArg (Inventory.expression root visit recognition).eval
      (environment_update_at root visit recognition frame occurrence).symm).trans (Expr.eval_update _ _ _))
theorem paid_value_at : (paidAt root visit recognition frame occurrence).2.2.1 =
    (Inventory.expression root visit recognition).eval (generatedEnvironmentAt root visit recognition frame occurrence) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
    (actual_equation_at root visit recognition frame occurrence)
theorem full_trace_fee_at : (fullTraceAt root visit recognition frame occurrence).length =
    remaining (rawAt root visit recognition frame occurrence).expression := substituted_charge _ _ _
theorem actual_paid_fee_at : (paidAt root visit recognition frame occurrence).2.1.2.length =
    remaining (rawAt root visit recognition frame occurrence).expression :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem source_material_at : (paidAt root visit recognition frame occurrence).2.2.2 =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      (E.Shared.base frame).root.toAuthoritativeRoot occurrence := rfl

theorem child_environment_at (index : Inventory.ChildIndex root recognition)
    (name : Inventory.ChildVar root recognition index)
    (coordinate : Inventory.P.Index root recognition index.1 index.2 (Inventory.childData root recognition index)) :
    generatedEnvironmentAt root visit recognition frame occurrence (.inr (.inl index)) name coordinate =
      Operation.SomePacket.action root recognition index.1 index.2 (Inventory.childData root recognition index) name.down
        (environmentAt root visit recognition frame occurrence (.inr (.inl index)) name coordinate) := rfl

theorem source_trace_fee_at : (sourceTraceAt root visit recognition frame occurrence).length =
    remaining (Query.expression root visit recognition) +
      Inventory.childCostAtCode root recognition (Inventory.oldCode root visit recognition) +
        Inventory.childCostAtCode root recognition (Inventory.nextCode root visit recognition) + 3 :=
  (execution_length _ _).trans (Inventory.branch_cost root visit recognition)

theorem actual_equation : type_of% (actual_equation_at root visit recognition frame (E.Shared.actualOccurrence frame)) :=
  actual_equation_at _ _ _ _ _
theorem actual_update : type_of% (actual_update_at root visit recognition frame (E.Shared.actualOccurrence frame)) :=
  actual_update_at _ _ _ _ _
theorem paid_value : type_of% (paid_value_at root visit recognition frame (E.Shared.actualOccurrence frame)) :=
  paid_value_at _ _ _ _ _
theorem full_trace_fee : type_of% (full_trace_fee_at root visit recognition frame (E.Shared.actualOccurrence frame)) :=
  full_trace_fee_at _ _ _ _ _
theorem actual_paid_preserved (event) (present : event ∈
    (SourceOperationPaidRelations.exposure (paid root visit recognition frame).2.1.2).trace) :
    event ∈ (written root visit recognition frame).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem full_trace_preserved (event) (present : event ∈
    (SourceOperationPaidRelations.exposure (fullTrace root visit recognition frame)).trace) :
    event ∈ (written root visit recognition frame).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event present
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
