import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Transport
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
namespace Lower.SourceFamily.Effect.Consumed
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance physicalGroups : ∀ t,AddCommGroup (Act.PhysicalValue root visit rec t) := inferInstance
local instance currentGroups (n : Nat) (t : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
 AddCommGroup (Lower.Value (Act.LowValue root visit rec) n t) := Lower.groups (Act.LowValue root visit rec) n t
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
abbrev originalBinding := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.lowBinding root visit rec
abbrev sourceInitial := initial root visit rec U7 calculus anchor sourceStage stage count
abbrev sourceCfg := firstCfg root visit rec U7 calculus anchor sourceStage stage
abbrev sourceLanguage := language root visit rec U7 calculus anchor sourceStage stage
abbrev Word (n : Nat) := History.Word (W:=Act.LowValue root visit rec) (X:=Act.LowVar root visit rec) (s:=Act.sort root rec) n
abbrev completion (n : Nat) := History.completion (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) n
abbrev sourceMap (n : Nat) := History.sourceMap (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) n
abbrev successor (n : Nat) := History.successor (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) n

theorem actual_environment (n : Nat) : type_of% (Environment.native_environment (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) (Future.First.actual_first_fee root visit rec U7 calculus anchor sourceStage stage count) n) :=
 Environment.native_environment _ _ _ _ (Future.First.actual_first_fee _ _ _ _ _ _ _ _ _) n

theorem actual_word (n : Nat) (word : Word root visit rec n) : type_of% (History.actual_word (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) (Future.First.actual_first_fee root visit rec U7 calculus anchor sourceStage stage count) n word) :=
 History.actual_word _ _ _ _ (Future.First.actual_first_fee _ _ _ _ _ _ _ _ _) n word

theorem actual_prefix (n bound : Nat) (word : Word root visit rec n) : type_of% (History.source_prefix (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) n bound word) := History.source_prefix _ _ _ _ n bound word

theorem actual_fibre (n : Nat) (left right : Word root visit rec n) : type_of% (History.source_fibre (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) n left right) := History.source_fibre _ _ _ _ n left right

theorem actual_successor (n : Nat) (word : Word root visit rec n) : type_of% (History.successor_source (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) n word) := History.successor_source _ _ _ _ n word

theorem whole_residual (n : Nat) (word : Word root visit rec n) : type_of% (Transport.whole_residual (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) (Future.First.actual_first_fee root visit rec U7 calculus anchor sourceStage stage count) n word) :=
 Transport.whole_residual _ _ _ _ (Future.First.actual_first_fee _ _ _ _ _ _ _ _ _) n word

theorem residual_injective (n : Nat) : type_of% (Transport.residual_injective (originalBinding root visit rec)
 (sourceInitial root visit rec U7 calculus anchor sourceStage stage count) (sourceCfg root visit rec U7 calculus anchor sourceStage stage)
 (sourceLanguage root visit rec U7 calculus anchor sourceStage stage) (Future.First.actual_first_fee root visit rec U7 calculus anchor sourceStage stage count) n) :=
 Transport.residual_injective _ _ _ _ (Future.First.actual_first_fee _ _ _ _ _ _ _ _ _) n

theorem actual_consumption (n bound : Nat) (word : Word root visit rec n) :
 type_of% (actual_environment root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_word root visit rec U7 calculus anchor sourceStage stage count n word) ∧
 type_of% (whole_residual root visit rec U7 calculus anchor sourceStage stage count n word) ∧
 type_of% (residual_injective root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_prefix root visit rec U7 calculus anchor sourceStage stage count n bound word) ∧
 type_of% (actual_successor root visit rec U7 calculus anchor sourceStage stage count n word) ∧
 type_of% (Lower.SourceFamily.Replay.Consumed.actual_consumption root visit rec U7 calculus anchor sourceStage stage count n) :=
 ⟨actual_environment _ _ _ _ _ _ _ _ _ n,actual_word _ _ _ _ _ _ _ _ _ n word,
 whole_residual _ _ _ _ _ _ _ _ _ n word,residual_injective _ _ _ _ _ _ _ _ _ n,
 actual_prefix _ _ _ _ _ _ _ _ _ n bound word,actual_successor _ _ _ _ _ _ _ _ _ n word,
 Lower.SourceFamily.Replay.Consumed.actual_consumption _ _ _ _ _ _ _ _ _ n⟩
end Lower.SourceFamily.Effect.Consumed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
