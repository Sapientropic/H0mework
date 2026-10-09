import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.Consumer
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Elimination
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController
namespace Lower.SourceFamily.Foresight.Consumed
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance physicalGroups : ∀ t, AddCommGroup (Act.PhysicalValue root visit rec t) := inferInstance
local instance currentGroups (n : Nat) (t : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
    AddCommGroup (Lower.Value (Act.LowValue root visit rec) n t) := Lower.groups (Act.LowValue root visit rec) n t
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
abbrev binding := Lower.SourceFamily.Replay.Activated.OriginalBinding.lowBinding root visit rec
abbrev initial := SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.initial root visit rec U7 calculus anchor sourceStage stage count
abbrev firstCfg := SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.firstCfg root visit rec U7 calculus anchor sourceStage stage
abbrev language := SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.language root visit rec U7 calculus anchor sourceStage stage
abbrev frame (n : Nat) := Lower.SourceFamily.Replay.Activated.frameAt root visit rec U7 calculus anchor sourceStage stage count n
abbrev seed (n : Nat) := Lower.SourceFamily.Replay.Activated.seedAt root visit rec U7 calculus anchor sourceStage stage count n
theorem actual_depth (n : Nat) : (frame root visit rec U7 calculus anchor sourceStage stage count n).depth = 0 := by
  cases n with
  | zero =>
      exact (Tail.cast_depth (language root visit rec U7 calculus anchor sourceStage stage) 1
        (⟨Lower.Stock.receiver (initial root visit rec U7 calculus anchor sourceStage stage count)
          (firstCfg root visit rec U7 calculus anchor sourceStage stage)
          (language root visit rec U7 calculus anchor sourceStage stage),
        Lower.Stock.seed (initial root visit rec U7 calculus anchor sourceStage stage count)
          (firstCfg root visit rec U7 calculus anchor sourceStage stage)
          (language root visit rec U7 calculus anchor sourceStage stage)⟩ :
          Lower.SourceFamily.Packet (W:=Act.LowValue root visit rec)
            (X:=(firstCfg root visit rec U7 calculus anchor sourceStage stage).LowVar) (s:=Act.sort root rec) 1)).trans rfl
  | succ _ => rfl
def face (n : Nat) := Contextual.Elimination.face (binding root visit rec) (n+1)
  (seed root visit rec U7 calculus anchor sourceStage stage count n)
  (frame root visit rec U7 calculus anchor sourceStage stage count n)
def high (n : Nat) := Contextual.Elimination.high (binding root visit rec) (n+1)
  (seed root visit rec U7 calculus anchor sourceStage stage count n)
  (frame root visit rec U7 calculus anchor sourceStage stage count n)
  (actual_depth root visit rec U7 calculus anchor sourceStage stage count n)
abbrev state (n : Nat) := Installed.nativeState (n+1)
  (seed root visit rec U7 calculus anchor sourceStage stage count n)
  (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev Word (n : Nat) (t) := Lower.SourceFamily.Foresight.Word (binding root visit rec)
  (state root visit rec U7 calculus anchor sourceStage stage count n) t 0

theorem actual_model (n : Nat) : type_of% (Contextual.Elimination.model_read (binding root visit rec) (n+1)
  (seed root visit rec U7 calculus anchor sourceStage stage count n)
  (frame root visit rec U7 calculus anchor sourceStage stage count n)
  (actual_depth root visit rec U7 calculus anchor sourceStage stage count n)) := Contextual.Elimination.model_read _ _ _ _ _

theorem actual_prefix (n bound : Nat) (t) (word : Word root visit rec U7 calculus anchor sourceStage stage count n t) :
  type_of% (Contextual.Elimination.source_prefix (binding root visit rec) (n+1)
    (seed root visit rec U7 calculus anchor sourceStage stage count n)
    (frame root visit rec U7 calculus anchor sourceStage stage count n)
    (actual_depth root visit rec U7 calculus anchor sourceStage stage count n) t bound word) := Contextual.Elimination.source_prefix _ _ _ _ _ _ _ _

theorem actual_fibre (n : Nat) (t) (left right : Word root visit rec U7 calculus anchor sourceStage stage count n t) :
  type_of% (Contextual.Elimination.source_fibre (binding root visit rec) (n+1)
    (seed root visit rec U7 calculus anchor sourceStage stage count n)
    (frame root visit rec U7 calculus anchor sourceStage stage count n)
    (actual_depth root visit rec U7 calculus anchor sourceStage stage count n) t left right) := Contextual.Elimination.source_fibre _ _ _ _ _ _ _ _

theorem source_successor (n : Nat) (t) (word : Word root visit rec U7 calculus anchor sourceStage stage count n t) :
  type_of% (Contextual.Elimination.next_source (binding root visit rec) (n+1)
    (seed root visit rec U7 calculus anchor sourceStage stage count n)
    (frame root visit rec U7 calculus anchor sourceStage stage count n)
    (actual_depth root visit rec U7 calculus anchor sourceStage stage count n) t word) := Contextual.Elimination.next_source _ _ _ _ _ _ _

theorem actual_consumption (n bound : Nat) (t) (word : Word root visit rec U7 calculus anchor sourceStage stage count n t) :
  type_of% (actual_model root visit rec U7 calculus anchor sourceStage stage count n) ∧
  type_of% (actual_prefix root visit rec U7 calculus anchor sourceStage stage count n bound t word) ∧
  type_of% (source_successor root visit rec U7 calculus anchor sourceStage stage count n t word) ∧
  type_of% (Lower.SourceFamily.Replay.Consumed.actual_consumption root visit rec U7 calculus anchor sourceStage stage count n) ∧
  type_of% (Lower.SourceFamily.Evaluated.Consumed.actual_source_component root visit rec U7 calculus anchor sourceStage stage count n) :=
  ⟨actual_model _ _ _ _ _ _ _ _ _ n, actual_prefix _ _ _ _ _ _ _ _ _ n bound t word,
    source_successor _ _ _ _ _ _ _ _ _ n t word,
    Lower.SourceFamily.Replay.Consumed.actual_consumption _ _ _ _ _ _ _ _ _ n,
    Lower.SourceFamily.Evaluated.Consumed.actual_source_component _ _ _ _ _ _ _ _ _ n⟩
end Lower.SourceFamily.Foresight.Consumed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
