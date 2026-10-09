import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot, AddCommGroup (PhysicalValue root visit rec slot) := inferInstance
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (LowValue root visit rec) (LowVar root visit rec) (sort root rec))))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=LowValue root visit rec) (Var:=LowVar root visit rec) (sort:=sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
variable (initial : type_of% frame)
theorem query_value : (paid root visit rec seed frame actual).2.2.1=
 (originalRaw root visit rec seed frame actual).expression.eval (readNext root visit rec frame actual) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans (Expr.eval_subst _ _ _)
theorem replay_fee : (replayTrace root visit rec seed frame actual).length = remaining (raw root visit rec seed frame actual).expression :=
 substituted_charge _ _ _
theorem query_paid_preserved (event) (present : event ∈ (SourceOperationPaidRelations.exposure (paid root visit rec seed frame actual).2.1.2).trace) :
 event ∈ (written root visit rec seed frame actual).trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem born_environment : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame
 (configuration root visit rec seed)).environment
 ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame
   (configuration root visit rec seed)).old.root.emitted
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame
   (configuration root visit rec seed)).old.visit.current) =
 physicalNext root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame) := rfl
theorem born_scalar : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame
 (configuration root visit rec seed)).inventory=
 some (scalarWritten root visit rec seed frame (A.Shared.actualOccurrence frame)) := rfl
theorem successor_valid : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.successor_valid
 frame (configuration root visit rec seed)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame (configuration root visit rec seed))) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.successor_valid _ _ _

theorem physical_next_source : (physicalNext root visit rec frame actual)=nextEnvironment root visit rec frame actual := rfl
theorem left_unchanged (slot) (name : PhysicalVar root visit rec slot) : physicalNext root visit rec frame actual slot (.inl name)=
 actualEnvironment root visit rec frame actual slot (.inl name) := rfl
theorem physical_written_preserved (event) (present : event ∈ (physicalWritten root visit rec seed frame actual).trace) :
 event ∈ (scalarWritten root visit rec seed frame actual).trace := by
 unfold scalarWritten
 cases (R.programme seed).nextInventory frame with
 | none => exact present
 | some original => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem old_scalar_preserved (original) (prior : (R.programme seed).nextInventory frame=some original)
 (event) (present : event ∈ original.trace) : event ∈ (scalarWritten root visit rec seed frame actual).trace := by
 unfold scalarWritten
 rw [prior]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem old_pair_preserved (original) (prior : (R.programme seed).nextPairInventory frame=some original)
 (event) (present : event ∈ original.trace) : event ∈ (pairWritten root visit rec seed frame actual).trace := by
 unfold pairWritten
 rw [prior]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem query_environment : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame
 (configuration root visit rec seed)).raw.environment =
 actionPairEnvironment root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame) := rfl

theorem right_complete_action (slot) (name : PhysicalVar root visit rec slot) :
 physicalNext root visit rec frame actual slot (.inr name)=
 ((D.binding root visit rec slot name).eval (rightOldEnvironment root visit rec frame actual),
  (D.binding root visit rec slot name).effect
   (rightOldEnvironment root visit rec frame actual) (rightEffectEnvironment root visit rec frame actual)) := by
 change (D.L.right (liftExpr (D.binding root visit rec slot name))).eval _ = _
 apply (Expr.eval_subst _ _ _).trans
 exact eval_liftExpr _ _ _

-- The native root occurrence in the physical right scope shifts by the original AST.
theorem right_core_action
 (datum : SourceOperationNative.Tree.Fold.Dependent.Branch.Node root visit rec) :
 let slot := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.coreSlot root rec
 ((physicalNext root visit rec frame actual slot (.inr (datum,.old))).1 (0:Fin 2),
  (physicalNext root visit rec frame actual slot (.inr (datum,.old))).2 (0:Fin 2)) =
 ((actualEnvironment root visit rec frame actual slot
   (.inr (SourceOperationNative.Tree.Fold.Dependent.Branch.nextNode root visit rec datum,.old))).1 (0:Fin 2),
  (actualEnvironment root visit rec frame actual slot
   (.inr (SourceOperationNative.Tree.Fold.Dependent.Branch.nextNode root visit rec datum,.old))).2 (0:Fin 2)) := by
 dsimp only
 rw [right_complete_action]
 apply Prod.ext <;> rfl

theorem born_actual_environment {nextCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
 (born root visit rec seed frame).registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence
  (born root visit rec seed frame) (current:=nextCurrent)) :
 actualEnvironment root visit rec (born root visit rec seed frame) supplied=
 physicalNext root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame) := rfl
theorem born_query_environment : (A.Shared.query (born root visit rec seed frame) (configuration root visit rec seed)).raw.environment =
 pairEnvironment (physicalNext root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame))
  (physicalNext root visit rec (A.epoch (born root visit rec seed frame))
    (A.Shared.actualOccurrence (born root visit rec seed frame))-
   physicalNext root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame)) := rfl
theorem two_math_query_environment : (A.Shared.query frame.mathNext.mathNext (configuration root visit rec seed)).raw.environment=
 actionPairEnvironment root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame.mathNext.mathNext) := rfl
theorem frames_query_environment (offset : Nat) : (A.Shared.query (frameAt root visit rec seed initial offset)
 (configuration root visit rec seed)).raw.environment=
 actionPairEnvironment root visit rec (A.epoch (frameAt root visit rec seed initial offset))
  (A.Shared.actualOccurrence (frameAt root visit rec seed initial offset)) := rfl
theorem actual_next (offset : Nat) : type_of% (A.Shared.actual_next initial (configuration root visit rec seed) offset) :=
 A.Shared.actual_next _ _ _
theorem actual_query (offset : Nat) : type_of% (A.Shared.actual_query initial (configuration root visit rec seed) offset) :=
 A.Shared.actual_query _ _ _


theorem actual_raw_face : (actualRawFace root visit rec seed frame).rootRead =
 actualRaw root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame) := rfl

theorem no_refill : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill
 (configuration root visit rec seed) frame) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill _ _
theorem wellFounded : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded
 (configuration root visit rec seed) frame) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded _ _


private def index (engine : Engine (A.Shared.process initial (configuration root visit rec seed))) : Nat := by
 rcases engine with ⟨count⟩
 exact count.down
private theorem raw_state (state : (runtime root visit rec seed initial).State) :
 SourceOperationInquiry.Context.raw (runtime root visit rec seed initial)
  (actualRawSource root visit rec seed initial) state =
 actualRaw root visit rec (A.epoch (frameAt root visit rec seed initial
  (index root visit rec seed initial state.engine)))
 (A.Shared.actualOccurrence (frameAt root visit rec seed initial
  (index root visit rec seed initial state.engine))) := by
 rcases state with ⟨⟨count⟩,activation⟩
 rfl

theorem raw_actual (offset : Nat) :
 SourceOperationInquiry.Context.raw (runtime root visit rec seed initial)
  (actualRawSource root visit rec seed initial) ((runtime root visit rec seed initial).stateAt offset) =
 actualRaw root visit rec (A.epoch (frameAt root visit rec seed initial offset))
 (A.Shared.actualOccurrence (frameAt root visit rec seed initial offset)) := by
 have indexEq : index root visit rec seed initial ((runtime root visit rec seed initial).stateAt offset).engine = offset := by
  have same := A.Shared.actual_node initial (configuration root visit rec seed) offset
  generalize engineEq : ((runtime root visit rec seed initial).stateAt offset).engine = engine at same ⊢
  rcases engine with ⟨hidden⟩
  have hiddenEq : hidden = ULift.up offset :=
   (A.Shared.process initial (configuration root visit rec seed)).erase_injective rfl rfl
    (congrArg RootInquiryProcessNode.erase same)
  subst hidden
  rfl
 exact (raw_state root visit rec seed initial _).trans
  (congrArg (fun i => actualRaw root visit rec (A.epoch (frameAt root visit rec seed initial i))
   (A.Shared.actualOccurrence (frameAt root visit rec seed initial i))) indexEq)

theorem environment_actual (offset : Nat) :
 SourceOperationInquiry.Context.readEnv (runtime root visit rec seed initial)
  (actualRawSource root visit rec seed initial) ((runtime root visit rec seed initial).stateAt offset) =
 actualEnvironment root visit rec (A.epoch (frameAt root visit rec seed initial offset))
 (A.Shared.actualOccurrence (frameAt root visit rec seed initial offset)) :=
 congrArg (fun raw => raw.environment) (raw_actual root visit rec seed initial offset)

theorem inverse_recovered (offset : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.source_execution
  (runtime root visit rec seed initial) (actualRawSource root visit rec seed initial)
  ((runtime root visit rec seed initial).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_execution _ _ _
theorem inverse_whole (offset : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.source_write
  (runtime root visit rec seed initial) (actualRawSource root visit rec seed initial)
  ((runtime root visit rec seed initial).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem inverse_next (offset : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.source_next
  (runtime root visit rec seed initial) (actualRawSource root visit rec seed initial)
  ((runtime root visit rec seed initial).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
