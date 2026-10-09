import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Action.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : C.Occurrence frame (current:=current))

theorem actual_equation_at : (rawAt root visit recognition U7 calculus anchor frame supplied).expression.eval
 (rawAt root visit recognition U7 calculus anchor frame supplied).environment =
 (nextExpressionAt root visit recognition U7 calculus anchor frame supplied).eval
  (generatedEnvironmentAt root visit recognition frame supplied) := Expr.eval_subst _ _ _
theorem environment_update_at : environmentAt root visit recognition frame supplied + incrementAt root visit recognition frame supplied =
 generatedEnvironmentAt root visit recognition frame supplied := add_sub_cancel _ _
theorem actual_update_at : (rawAt root visit recognition U7 calculus anchor frame supplied).expression.eval
 (rawAt root visit recognition U7 calculus anchor frame supplied).environment =
 (nextExpressionAt root visit recognition U7 calculus anchor frame supplied).eval (environmentAt root visit recognition frame supplied) +
 (nextExpressionAt root visit recognition U7 calculus anchor frame supplied).effect
  (environmentAt root visit recognition frame supplied) (incrementAt root visit recognition frame supplied) :=
 (actual_equation_at root visit recognition U7 calculus anchor frame supplied).trans
  ((congrArg (nextExpressionAt root visit recognition U7 calculus anchor frame supplied).eval
    (environment_update_at root visit recognition frame supplied).symm).trans (Expr.eval_update _ _ _))
theorem paid_value_at : (paidAt root visit recognition U7 calculus anchor frame supplied).2.2.1 =
 (Dynamic.paidFor root visit recognition U7 calculus anchor frame (Dynamic.nextRead root visit recognition frame) supplied).2.2.1 := by
 have first := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (E.Shared.base frame).root.toAuthoritativeRoot
  (fun {_current} occurrence => rawAt root visit recognition U7 calculus anchor frame occurrence) supplied
 have next := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (E.Shared.base frame).root.toAuthoritativeRoot
  (fun {_current} occurrence => Dynamic.rawFor root visit recognition U7 calculus anchor frame
   (Dynamic.nextRead root visit recognition frame) occurrence) supplied
 exact first.trans ((actual_equation_at root visit recognition U7 calculus anchor frame supplied).trans next.symm)
theorem full_trace_fee_at : (fullTraceAt root visit recognition U7 calculus anchor frame supplied).length =
 remaining (rawAt root visit recognition U7 calculus anchor frame supplied).expression := substituted_charge _ _ _
theorem actual_paid_fee_at : (paidAt root visit recognition U7 calculus anchor frame supplied).2.1.2.length =
 remaining (rawAt root visit recognition U7 calculus anchor frame supplied).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem source_trace_fee_at : (sourceTraceAt root visit recognition U7 calculus anchor frame supplied).length =
 remaining (nextExpressionAt root visit recognition U7 calculus anchor frame supplied) := execution_length _ _
theorem source_material_at : (paidAt root visit recognition U7 calculus anchor frame supplied).2.2.2 =
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
  (E.Shared.base frame).root.toAuthoritativeRoot supplied := rfl

theorem child_environment_at (index : Inventory.ChildIndex root recognition)
 (name : Inventory.ChildVar root recognition index)
 (coordinate : Inventory.P.Index root recognition index.1 index.2 (Inventory.childData root recognition index)) :
 generatedEnvironmentAt root visit recognition frame supplied (.inl (.inl (.inr (.inl index)))) name coordinate =
 Operation.SomePacket.action root recognition index.1 index.2 (Inventory.childData root recognition index) name.down
  (environmentAt root visit recognition frame supplied (.inl (.inl (.inr (.inl index)))) name coordinate) := by
 change (CurrentChild.embed root visit recognition (Observer.Action.binding root visit recognition (.inl (.inr (.inl index))) name)).eval
  (environmentAt root visit recognition frame supplied) coordinate = _
 have projected : environmentAt root visit recognition frame supplied =
  Actor.Extension.environment (Observer.Value root visit recognition) (Observer.Variable root visit recognition)
   (CurrentChild.Output root visit recognition)
   (fun slot name => environmentAt root visit recognition frame supplied (.inl slot) name) := by
  funext slot name
  cases slot with
  | inl original => rfl
  | inr extra => exact PEmpty.elim name
 rw [projected,Actor.Extension.embed_eval]
 rfl

theorem actual_paid_preserved (event) (present : event ∈
 (SourceOperationPaidRelations.exposure (paidAt root visit recognition U7 calculus anchor frame supplied).2.1.2).trace) :
 event ∈ (writtenAt root visit recognition U7 calculus anchor frame supplied).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem full_trace_preserved (event) (present : event ∈
 (SourceOperationPaidRelations.exposure (fullTraceAt root visit recognition U7 calculus anchor frame supplied)).trace) :
 event ∈ (writtenAt root visit recognition U7 calculus anchor frame supplied).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event present

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
