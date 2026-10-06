import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Source
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition
open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)

theorem child_value (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) :
    childValueAtCode root visit recognition code =
      match stepSuccessor? (P.step root recognition code) with
      | none => (0,0)
      | some successor => childInjection root visit recognition ⟨code,successor⟩
          ((childRaw root recognition ⟨code,successor⟩).expression.eval
            (childRaw root recognition ⟨code,successor⟩).environment) := by
  classical
  unfold childValueAtCode childExpressionAtCode
  split
  · rename_i same
    rw [same]
    rfl
  · rename_i same
    rw [same]
    change childInjection root visit recognition _ ((childEmbed root visit recognition _ _).eval _) = _
    rw [child_embed_eval]

theorem child_first_zero (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) :
    (childValueAtCode root visit recognition code).1=0 := by
  rw [child_value]
  split <;> rfl

theorem source_inventory : (expression root visit recognition).eval (environment root visit recognition) =
    ((Query.expression root visit recognition).eval (Query.environment root visit recognition),
      (childValueAtCode root visit recognition (oldCode root visit recognition)).2 +
        (childValueAtCode root visit recognition (nextCode root visit recognition)).2) := by
  change oldInjection root visit recognition ((embed root visit recognition (Query.expression root visit recognition)).eval _) +
    (childValueAtCode root visit recognition _ + childValueAtCode root visit recognition _) = _
  rw [embed_eval]
  apply Prod.ext
  · change (Query.expression root visit recognition).eval (Query.environment root visit recognition) +
      ((childValueAtCode root visit recognition _).1+(childValueAtCode root visit recognition _).1)=_
    rw [child_first_zero,child_first_zero,zero_add,add_zero]
  · exact zero_add _

theorem paid_inventory : (paid root visit recognition).2.2.1 =
    ((Query.expression root visit recognition).eval (Query.environment root visit recognition),
      (childValueAtCode root visit recognition (oldCode root visit recognition)).2 +
        (childValueAtCode root visit recognition (nextCode root visit recognition)).2) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value root.toAuthoritativeRoot
    (reader root visit recognition) (root.emitted visit.current)).trans (source_inventory root visit recognition)

theorem actual_next_operation : (paid root visit recognition).2.2.1.1.2.1 +
    (paid root visit recognition).2.2.1.1.2.2 = Finsupp.single (Operation.sourceOperation root visit recognition) 1 := by
  rw [paid_inventory]
  have oldRead := Query.source_inventory root visit recognition
  rw [oldRead,Query.actual_bundle]
  exact add_sub_cancel _ _

theorem child_expression_cost (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot) :
    remaining (childExpressionAtCode root visit recognition code) = childCostAtCode root recognition code := by
  unfold childExpressionAtCode childCostAtCode
  split
  · rfl
  · change remaining (childEmbed root visit recognition _ _) + 1 = _
    rw [child_embed_charge]

theorem branch_cost : remaining (expression root visit recognition) =
    remaining (Query.expression root visit recognition) +
      childCostAtCode root recognition (oldCode root visit recognition) +
        childCostAtCode root recognition (nextCode root visit recognition) + 3 := by
  simp only [expression,remaining,outputEmbed,embed_charge,child_expression_cost]
  omega

theorem trace_fee : (trace root visit recognition).length =
    remaining (Query.expression root visit recognition) +
      childCostAtCode root recognition (oldCode root visit recognition) +
        childCostAtCode root recognition (nextCode root visit recognition) + 3 :=
  (execution_length _ _).trans (branch_cost root visit recognition)

theorem core_cost : (paid root visit recognition).2.1.2.length =
    (Query.paid root visit recognition).2.1.2.length +
      childCostAtCode root recognition (oldCode root visit recognition) +
        childCostAtCode root recognition (nextCode root visit recognition) + 3 := by
  have first := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history root.toAuthoritativeRoot
    (reader root visit recognition) (root.emitted visit.current)
  have second := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history root.toAuthoritativeRoot
    (Query.reader root visit recognition) (root.emitted visit.current)
  calc
    _ = remaining (expression root visit recognition) := first
    _ = remaining (Query.expression root visit recognition) +
        childCostAtCode root recognition (oldCode root visit recognition) +
          childCostAtCode root recognition (nextCode root visit recognition) + 3 := branch_cost root visit recognition
    _ = _ := congrArg (fun budget => budget + childCostAtCode root recognition (oldCode root visit recognition) +
      childCostAtCode root recognition (nextCode root visit recognition) + 3) second.symm

theorem old_child_cost : (childTraceAtCode root visit recognition (oldCode root visit recognition)).length =
    childCostAtCode root recognition (oldCode root visit recognition) :=
  (execution_length _ _).trans (child_expression_cost root visit recognition _)
theorem next_child_cost : (childTraceAtCode root visit recognition (nextCode root visit recognition)).length =
    childCostAtCode root recognition (nextCode root visit recognition) :=
  (execution_length _ _).trans (child_expression_cost root visit recognition _)

theorem old_embedding_value (term : Expr (Actor.Value root visit recognition) (Actor.Variable root visit recognition) (.inr PUnit.unit)) :
    (oldEmbedding root visit recognition term).eval (environment root visit recognition) =
      ((term.eval (Actor.environment root visit recognition),0),0) := by
  change oldInjection root visit recognition
    ((embed root visit recognition (Query.embedOutput root visit recognition term)).eval (environment root visit recognition)) = _
  rw [embed_eval,Query.embed_output]
  rfl


mutual
 private theorem trace_map {T U : Type u} (map : T → U) (tree : RootedAccountedUnfolding T) :
     (tree.map map).trace=tree.trace.map map := by
   cases tree with
   | occur origin branches =>
       change map origin :: RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.mapBranches map branches) = _
       exact congrArg (List.cons _) (branches_map map branches)
 private theorem branches_map {T U : Type u} (map : T → U) (branches : AccountedBranches T) :
     RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.mapBranches map branches) =
       (RootedAccountedUnfolding.traceBranches branches).map map := by
   cases branches with
   | nil => rfl
   | cons head tail =>
       change (head.map map).trace ++ RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.mapBranches map tail) =
         (head.trace ++ RootedAccountedUnfolding.traceBranches tail).map map
       rw [trace_map,branches_map,List.map_append]
end

theorem old_trace_order : (oldStock root visit recognition).trace =
    (Actor.Installation.stock root visit recognition).trace.map (oldEventMap root visit recognition) := trace_map _ _
theorem original_child_trace_order (index : ChildIndex root recognition) :
    (originalChildStock root visit recognition index).trace =
      (SourceOperationPaidRelations.exposure
        (Operation.SomePacket.paid root recognition index.1 index.2 (childData root recognition index)
          (P.source_seed_eq root recognition index.1 index.2) (P.target_seed_eq root recognition index.1 index.2)).2.1.2).trace.map
            (childEventMap root visit recognition index) := trace_map _ _

theorem child_raw_cost (index : ChildIndex root recognition) : remaining (childRaw root recognition index).expression =
    (Operation.SomePacket.indices root recognition index.1 index.2 (childData root recognition index)).length * 4 :=
  (execution_length _ _).symm.trans
    (Operation.SomePacket.exact_fee root recognition index.1 index.2 (childData root recognition index)
      (P.source_seed_eq root recognition index.1 index.2) (P.target_seed_eq root recognition index.1 index.2))

private theorem base_preserved {T : Type u} (base : RootedAccountedUnfolding T)
    (child : Option (RootedAccountedUnfolding T)) (event : T) (present : event ∈ base.trace) :
    event ∈ (match child with | none => base | some supplied => SourceHistoryCommon.seed base supplied).trace := by
  cases child with
  | none => exact present
  | some supplied => exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
private def contains {T : Type u} (child : Option (RootedAccountedUnfolding T)) (event : T) : Prop :=
  match child with | none => False | some supplied => event ∈ supplied.trace
private theorem child_preserved {T : Type u} (base : RootedAccountedUnfolding T)
    (child : Option (RootedAccountedUnfolding T)) (event : T) (present : contains child event) :
    event ∈ (match child with | none => base | some supplied => SourceHistoryCommon.seed base supplied).trace := by
  cases child with
  | none => exact False.elim present
  | some supplied => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem old_preserved (event) (present : event ∈ (oldStock root visit recognition).trace) :
    event ∈ (stock root visit recognition).trace :=
  base_preserved _ _ event (base_preserved _ _ event ((SourceHistoryCommon.parallel_left _ _ _).1 event present))
theorem new_paid_preserved (event) (present : event ∈ (paidStock root visit recognition).trace) :
    event ∈ (stock root visit recognition).trace :=
  base_preserved _ _ event (base_preserved _ _ event ((SourceHistoryCommon.parallel_right _ _ _).1 event present))
theorem old_child_preserved (event) (present : contains (childStock root visit recognition).1 event) :
    event ∈ (stock root visit recognition).trace :=
  base_preserved _ _ event (child_preserved _ _ event present)
theorem next_child_preserved (event) (present : contains (childStock root visit recognition).2 event) :
    event ∈ (stock root visit recognition).trace := child_preserved _ _ event present
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
