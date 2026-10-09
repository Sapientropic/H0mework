import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Action.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController CofinalHistorySettlement
namespace E.Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (query nextBorn presentation actual_query actual_next actual_answer)
end E.Shared
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (frame : Action.Frame root visit recognition)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (Inventory.Value root visit recognition) (Inventory.Variable root visit recognition) (Inventory.resultSlot root recognition))))
theorem source_material : (face root visit recognition frame seed).rootRead=
    material root visit recognition (E.epoch frame) seed (E.Shared.actualOccurrence frame) := rfl
theorem original_query : (E.Shared.query frame (configuration root visit recognition seed)).raw=
    ((R.programme seed).datum (E.epoch frame)).reader (E.Shared.actualOccurrence frame) := rfl
theorem installed_environment {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Action.C.Occurrence frame (current:=current)) : sourceEnvironmentRead root visit recognition frame seed occurrence=
    Action.generatedEnvironmentAt root visit recognition frame occurrence := rfl
theorem born_environment : (E.Shared.nextBorn frame (configuration root visit recognition seed)).environment
    ((E.Shared.nextBorn frame (configuration root visit recognition seed)).old.root.emitted
      (E.Shared.nextBorn frame (configuration root visit recognition seed)).old.visit.current)=
    Action.generatedEnvironmentAt root visit recognition (E.epoch frame) (E.Shared.actualOccurrence frame) := rfl
theorem born_child_environment (index : Inventory.ChildIndex root recognition)
    (name : Inventory.ChildVar root recognition index)
    (coordinate : Inventory.P.Index root recognition index.1 index.2 (Inventory.childData root recognition index)) :
    (E.Shared.nextBorn frame (configuration root visit recognition seed)).environment
      ((E.Shared.nextBorn frame (configuration root visit recognition seed)).old.root.emitted
        (E.Shared.nextBorn frame (configuration root visit recognition seed)).old.visit.current)
          (.inr (.inl index)) name coordinate =
      Operation.SomePacket.action root recognition index.1 index.2 (Inventory.childData root recognition index) name.down
        (Action.environmentAt root visit recognition (E.epoch frame) (E.Shared.actualOccurrence frame)
          (.inr (.inl index)) name coordinate) := by
  rw [born_environment]
  exact Action.child_environment_at root visit recognition (E.epoch frame) (E.Shared.actualOccurrence frame) index name coordinate
theorem born_scalar : (E.Shared.nextBorn frame (configuration root visit recognition seed)).inventory=
    some (nextScalar root visit recognition frame seed) := rfl
theorem born_pair : (E.Shared.nextBorn frame (configuration root visit recognition seed)).pairInventory=
    some (nextPair root visit recognition frame seed) := rfl
theorem accumulated_preserved (event) (present : event ∈ (accumulated root visit recognition frame).trace) :
    event ∈ (nextScalar root visit recognition frame seed).trace := by
  unfold nextScalar
  cases (R.programme seed).nextInventory frame with
  | none => exact present
  | some original => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem original_scalar_write (original) (hasOriginal : (R.programme seed).nextInventory frame=some original)
    (event) (present : event ∈ original.trace) : event ∈ (nextScalar root visit recognition frame seed).trace := by
  unfold nextScalar
  rw [hasOriginal]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem action_preserved (event) (present : event ∈ (Action.written root visit recognition frame).trace) :
    event ∈ (nextScalar root visit recognition frame seed).trace :=
  accumulated_preserved root visit recognition frame seed event ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
theorem scalar_preserved (prior) (hasPrior : frame.inventory=some prior) (event) (present : event ∈ prior.trace) :
    event ∈ (nextScalar root visit recognition frame seed).trace := by
  apply accumulated_preserved root visit recognition frame seed event
  unfold accumulated
  rw [hasPrior]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
theorem pair_written_preserved (event) (present : event ∈ (pairWritten root visit recognition frame).trace) :
    event ∈ (nextPair root visit recognition frame seed).trace := by
  unfold nextPair
  cases (R.programme seed).nextPairInventory frame with
  | none => exact present
  | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem old_pair_preserved (prior) (hasPrior : (R.programme seed).nextPairInventory frame=some prior)
    (event) (present : event ∈ prior.trace) : event ∈ (nextPair root visit recognition frame seed).trace := by
  unfold nextPair
  rw [hasPrior]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem math_environment {current : frame.V.Current}
    (occurrence : frame.old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    frame.mathNext.environment occurrence=frame.environment occurrence := rfl
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem initial_binding : Action.generatedEnvironment root visit recognition (initial root visit recognition U7 calculus)=
    SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment (Action.binding root visit recognition)
      (Inventory.environment root visit recognition) := rfl
theorem initial_source : initial root visit recognition U7 calculus=Inventory.Installation.initial root visit recognition U7 calculus := rfl
theorem actual_initial : (runtime root visit recognition U7 calculus).initialState.engine.node=
    .active (E.Shared.presentation (initial root visit recognition U7 calculus) (programme root visit recognition U7 calculus)) := rfl
theorem actual_input (stage : Nat) : type_of%
    (E.Shared.actual_query (initial root visit recognition U7 calculus) (programme root visit recognition U7 calculus) stage) :=
  E.Shared.actual_query _ _ stage
theorem actual_next (stage : Nat) : type_of%
    (E.Shared.actual_next (initial root visit recognition U7 calculus) (programme root visit recognition U7 calculus) stage) :=
  E.Shared.actual_next _ _ stage
theorem actual_answer (stage : Nat) : type_of%
    (E.Shared.actual_answer (initial root visit recognition U7 calculus) (programme root visit recognition U7 calculus) stage) :=
  E.Shared.actual_answer _ _ stage

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
