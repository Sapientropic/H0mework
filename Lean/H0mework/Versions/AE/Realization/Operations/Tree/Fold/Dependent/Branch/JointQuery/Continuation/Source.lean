import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Installation
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Action.History.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
-- The source action changes the complete environment; the paid state and stock stay source-generated.
def frame := {JointQuery.initial root visit recognition U7 calculus with
 environment:=fun {_current} _ => Action.sourceEnvironment root visit recognition
 inventory:=some (Action.History.stock root visit recognition)}
abbrev seed := SourceHistoryCommon.seed (Action.History.stock root visit recognition)
 (RootedAccountedUnfolding.zero (CofinalHistorySettlement.PresentedRelationEventAt.generator
 (frame root visit recognition U7 calculus).registered.input.expression))
abbrev runtime := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.runtime
 (seed root visit recognition U7 calculus) (frame root visit recognition U7 calculus)
abbrev generated := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.generated
 (seed root visit recognition U7 calculus) (frame root visit recognition U7 calculus)
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
