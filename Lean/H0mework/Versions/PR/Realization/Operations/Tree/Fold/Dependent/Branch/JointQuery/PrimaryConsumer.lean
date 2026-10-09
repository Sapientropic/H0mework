import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Primary.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Readback
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Action.History.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem primary_initial_inventory : (Primary.initial root visit recognition U7 calculus).inventory=some (Action.History.stock root visit recognition) := rfl
theorem source_seed_preserved (event) (present : event ∈ (jointSeed root visit recognition).trace) :
 event ∈ (Primary.seed root visit recognition U7 calculus).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event (Action.History.literal_old_stock root visit recognition event present)
theorem current_scalar_stock : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.initial_seed_preserved
 (Primary.seed root visit recognition U7 calculus) (Primary.initial root visit recognition U7 calculus)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.initial_seed_preserved _ _
theorem actual_born : type_of% (Primary.born_inventory root visit recognition U7 calculus 0) := Primary.born_inventory _ _ _ _ _ 0
theorem actual_main_query (count : Nat) : type_of% (Primary.actual_input root visit recognition U7 calculus count) := Primary.actual_input _ _ _ _ _ count
theorem actual_main_next (count : Nat) : type_of% (Primary.actual_next root visit recognition U7 calculus count) := Primary.actual_next _ _ _ _ _ count
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
