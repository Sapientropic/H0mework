import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
  (programme runtime frameAt face)
end A
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (root visit actualOccurrence baseRoot queryRoot resultRoot consumerRoot baseInstallation queryLaw resultLaw consumerLaw compilationLaw)
end Shared
end E
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

abbrev initial := Born.frame root visit recognition U7 calculus count
def seed := SourceHistoryCommon.seed (Born.stock root visit recognition U7 calculus count)
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
    (initial root visit recognition U7 calculus count).registered.input.expression))
abbrev configuration := A.programme (seed root visit recognition U7 calculus count)
abbrev runtime := A.runtime (seed root visit recognition U7 calculus count) (initial root visit recognition U7 calculus count)
abbrev frameAt (stage : Nat) := A.frameAt (seed root visit recognition U7 calculus count)
  (initial root visit recognition U7 calculus count) stage
abbrev initialRoot := E.Shared.root (initial root visit recognition U7 calculus count)
  (configuration root visit recognition U7 calculus count)
abbrev initialVisit := E.Shared.visit (initial root visit recognition U7 calculus count)
  (configuration root visit recognition U7 calculus count)
abbrev materialFace (stage : Nat) := A.face (seed root visit recognition U7 calculus count)
  (frameAt root visit recognition U7 calculus count stage)

def oldInstallation :=
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (initial root visit recognition U7 calculus count).currentState.root.source.base
    (SourceOperationInquiry.Context.Installation.component (E.epoch (initial root visit recognition U7 calculus count)))).trans
  (E.Shared.baseInstallation (initial root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus count)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (E.Shared.baseRoot (initial root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus count)).source.base
    (E.Shared.queryLaw (E.epoch (initial root visit recognition U7 calculus count)) (configuration root visit recognition U7 calculus count))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (E.Shared.queryRoot (initial root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus count)).source.base
    (E.Shared.resultLaw (E.epoch (initial root visit recognition U7 calculus count)) (configuration root visit recognition U7 calculus count))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (E.Shared.resultRoot (initial root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus count)).source.base
    (E.Shared.consumerLaw (E.epoch (initial root visit recognition U7 calculus count)) (configuration root visit recognition U7 calculus count))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (E.Shared.consumerRoot (initial root visit recognition U7 calculus count) (configuration root visit recognition U7 calculus count)).source.base
    (E.Shared.compilationLaw (E.epoch (initial root visit recognition U7 calculus count)) (configuration root visit recognition U7 calculus count)))

def material := (Born.material root visit recognition U7 calculus count,
  seed root visit recognition U7 calculus count, oldInstallation root visit recognition U7 calculus count)
abbrev actualGenerated := (Receipt.generated root visit recognition U7 calculus count,
  runtime root visit recognition U7 calculus count, material root visit recognition U7 calculus count)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
