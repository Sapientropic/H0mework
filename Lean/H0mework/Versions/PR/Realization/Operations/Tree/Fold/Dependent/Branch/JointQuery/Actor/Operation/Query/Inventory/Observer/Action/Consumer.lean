import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Action.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : C.Occurrence frame (current:=current))

theorem old_embed_eval_at {slot : Inventory.Slot root recognition}
    (term : Expr (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition) slot) :
    (Observer.embed root visit recognition term).eval (environmentAt root visit recognition frame occurrence) =
      term.eval (oldEnvironmentAt root visit recognition frame occurrence) := by
  induction term with
  | var => rfl
  | const => rfl
  | add first second one two => exact congrArg₂ (·+·) one two
  | linear operation argument previous => exact congrArg operation previous
  | bilinear operation first second one two => exact congrArg₂ (fun x y => operation x y) one two

theorem actual_equation_at : (rawAt root visit recognition U7 calculus anchor frame occurrence).expression.eval
    (rawAt root visit recognition U7 calculus anchor frame occurrence).environment =
      (observerSyntax root visit recognition U7 calculus anchor).eval
        (generatedEnvironmentAt root visit recognition frame occurrence) := Expr.eval_subst _ _ _
theorem environment_update_at : environmentAt root visit recognition frame occurrence +
    incrementAt root visit recognition frame occurrence = generatedEnvironmentAt root visit recognition frame occurrence :=
  add_sub_cancel _ _
theorem actual_update_at : (rawAt root visit recognition U7 calculus anchor frame occurrence).expression.eval
    (rawAt root visit recognition U7 calculus anchor frame occurrence).environment =
      (observerSyntax root visit recognition U7 calculus anchor).eval (environmentAt root visit recognition frame occurrence) +
        (observerSyntax root visit recognition U7 calculus anchor).effect
          (environmentAt root visit recognition frame occurrence) (incrementAt root visit recognition frame occurrence) :=
  (actual_equation_at root visit recognition U7 calculus anchor frame occurrence).trans
    ((congrArg (observerSyntax root visit recognition U7 calculus anchor).eval
      (environment_update_at root visit recognition frame occurrence).symm).trans (Expr.eval_update _ _ _))
theorem paid_value_at : (paidAt root visit recognition U7 calculus anchor frame occurrence).2.2.1 =
    (observerSyntax root visit recognition U7 calculus anchor).eval
      (generatedEnvironmentAt root visit recognition frame occurrence) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
    (actual_equation_at root visit recognition U7 calculus anchor frame occurrence)
theorem full_trace_fee_at : (fullTraceAt root visit recognition U7 calculus anchor frame occurrence).length =
    remaining (rawAt root visit recognition U7 calculus anchor frame occurrence).expression := substituted_charge _ _ _
theorem actual_paid_fee_at : (paidAt root visit recognition U7 calculus anchor frame occurrence).2.1.2.length =
    remaining (rawAt root visit recognition U7 calculus anchor frame occurrence).expression :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem source_trace_fee_at : (sourceTraceAt root visit recognition U7 calculus anchor frame occurrence).length =
    remaining (observerSyntax root visit recognition U7 calculus anchor) := execution_length _ _
theorem source_material_at : (paidAt root visit recognition U7 calculus anchor frame occurrence).2.2.2 =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      (E.Shared.base frame).root.toAuthoritativeRoot occurrence := rfl

theorem child_environment_at (index : Inventory.ChildIndex root recognition)
    (name : Inventory.ChildVar root recognition index)
    (coordinate : Inventory.P.Index root recognition index.1 index.2 (Inventory.childData root recognition index)) :
    generatedEnvironmentAt root visit recognition frame occurrence (.inl (.inr (.inl index))) name coordinate =
      Operation.SomePacket.action root recognition index.1 index.2 (Inventory.childData root recognition index) name.down
        (environmentAt root visit recognition frame occurrence (.inl (.inr (.inl index))) name coordinate) := by
  change (Observer.embed root visit recognition (Inventory.Action.binding root visit recognition (.inr (.inl index)) name)).eval
    (environmentAt root visit recognition frame occurrence) coordinate = _
  rw [old_embed_eval_at]
  rfl

def pointAt (row : Observer.Row root recognition) :=
  environmentAt root visit recognition frame occurrence (.inl (.inr (.inl row.1))) ⟨row.2⟩ row.2
def nextPointAt (row : Observer.Row root recognition) :=
  generatedEnvironmentAt root visit recognition frame occurrence (.inl (.inr (.inl row.1))) ⟨row.2⟩ row.2

theorem next_point_at (row : Observer.Row root recognition) : nextPointAt root visit recognition frame occurrence row =
    Observer.action root recognition row (pointAt root visit recognition frame occurrence row) :=
  child_environment_at root visit recognition frame occurrence row.1 ⟨row.2⟩ row.2

theorem actual_model_at (row : Observer.Row root recognition) :
    Observer.modelAction root recognition row (Observer.modelProjection root recognition row
      (pointAt root visit recognition frame occurrence row)) =
      Observer.modelProjection root recognition row (nextPointAt root visit recognition frame occurrence row) :=
  (SourceGeneratedActionObservationHistory.modelAction_source (Observer.action root recognition row)
    (Observer.measurement root recognition row) (pointAt root visit recognition frame occurrence row)).trans
    (congrArg (Observer.modelProjection root recognition row) (next_point_at root visit recognition frame occurrence row).symm)

theorem actual_paid_preserved (event) (present : event ∈
    (SourceOperationPaidRelations.exposure (paidAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame)).2.1.2).trace) :
    event ∈ (written root visit recognition U7 calculus anchor frame).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem full_trace_preserved (event) (present : event ∈
    (SourceOperationPaidRelations.exposure (fullTraceAt root visit recognition U7 calculus anchor frame (E.Shared.actualOccurrence frame))).trace) :
    event ∈ (written root visit recognition U7 calculus anchor frame).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem source_paid_value : (paid root visit recognition U7 calculus anchor).2.2.1 =
    (observerSyntax root visit recognition U7 calculus anchor).eval
      (generatedEnvironmentAt root visit recognition (initial root visit recognition U7 calculus anchor)
        (E.Shared.actualOccurrence (initial root visit recognition U7 calculus anchor))) :=
  paid_value_at root visit recognition U7 calculus anchor (initial root visit recognition U7 calculus anchor)
    (E.Shared.actualOccurrence (initial root visit recognition U7 calculus anchor))

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
