import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace F
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Activated (frameAt cfg)
end F
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action (PhysicalValue LowValue LowVar sort)
end Act
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
abbrev initial := F.frameAt root visit rec U7 calculus anchor sourceStage stage count
abbrev firstCfg := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.configuration (F.cfg root visit rec U7 calculus anchor sourceStage stage)
theorem language : (firstCfg root visit rec U7 calculus anchor sourceStage stage).LowVar=Act.LowVar root visit rec := rfl
abbrev process := Lower.Run.process (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage)
abbrev runtime := Lower.Run.runtime (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage)
abbrev actualFrame := Lower.Run.frameAt (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage)
abbrev actualCfg := Lower.Run.cfgAt (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage)

theorem actual_node (n : Nat) : type_of% (Lower.Run.actual_node (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) n) := Lower.Run.actual_node _ _ _ _
theorem actual_next (n : Nat) : type_of% (Lower.Run.actual_next (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) n) := Lower.Run.actual_next _ _ _ _
theorem actual_receipt (n : Nat) : type_of% (Lower.Run.actual_receipt (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) n) := Lower.Run.actual_receipt _ _ _ _
theorem actual_whole_next (n : Nat) : type_of% (Lower.Run.next_full_root (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) n) := Lower.Run.next_full_root _ _ _ _
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
