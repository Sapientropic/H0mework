import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Fields
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Consumed
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
abbrev nativeCfg := F.cfg root visit rec U7 calculus anchor sourceStage stage
abbrev sourceFrame := initial root visit rec U7 calculus anchor sourceStage stage count
abbrev faceAt := Lower.Facets.actualFaceAt (sourceFrame root visit rec U7 calculus anchor sourceStage stage count)
 (nativeCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage)
abbrev facesAt := Lower.Facets.facesAt (sourceFrame root visit rec U7 calculus anchor sourceStage stage count)
 (nativeCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage)
abbrev packetAt := Lower.Fields.packet (sourceFrame root visit rec U7 calculus anchor sourceStage stage count)
 (nativeCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage)

theorem actual_packet (n : Nat) : type_of% (Lower.Facets.actual_source_read
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage count) (nativeCfg root visit rec U7 calculus anchor sourceStage stage)
 (language root visit rec U7 calculus anchor sourceStage stage) n) := Lower.Facets.actual_source_read _ _ _ _

theorem actual_dual (n : Nat) : type_of% (Lower.Facets.installed_dual
 (sourceFrame root visit rec U7 calculus anchor sourceStage stage count) (nativeCfg root visit rec U7 calculus anchor sourceStage stage)
 (language root visit rec U7 calculus anchor sourceStage stage) n) := Lower.Facets.installed_dual _ _ _ _

def actionAt (n : Nat) := Lower.Run.generated (sourceFrame root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) n

theorem born_inherits_actual_packet (n : Nat) : type_of% ((actionAt root visit rec U7 calculus anchor sourceStage stage count n).target.oldOutcome_heq
 (faceAt root visit rec U7 calculus anchor sourceStage stage count n).projection) :=
 (actionAt root visit rec U7 calculus anchor sourceStage stage count n).target.oldOutcome_heq
 (faceAt root visit rec U7 calculus anchor sourceStage stage count n).projection

theorem actual_receipt_with_packet (n : Nat) : type_of%
 (actual_receipt root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_whole_next root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (born_inherits_actual_packet root visit rec U7 calculus anchor sourceStage stage count n) :=
 ⟨actual_receipt _ _ _ _ _ _ _ _ _ _,actual_whole_next _ _ _ _ _ _ _ _ _ _,born_inherits_actual_packet _ _ _ _ _ _ _ _ _ _⟩
end Consumed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
