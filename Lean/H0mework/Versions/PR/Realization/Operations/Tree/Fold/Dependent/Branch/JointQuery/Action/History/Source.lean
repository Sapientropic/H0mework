import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Action.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Installation
import H0mework.Realization.Operations.Execution.Relations.History.Events
import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Exposure

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.History
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)

def reader {_current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt _current) :=
  Action.raw root visit recognition
abbrev paidResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  root.toAuthoritativeRoot (reader root visit recognition) (root.emitted visit.current)
abbrev paidExposure := SourceOperationPaidRelations.exposure (paidResult root visit recognition).2.1.2
abbrev fullExposure := SourceOperationPaidRelations.exposure (Action.fullTrace root visit recognition)
def stock := SourceHistoryCommon.seed (JointQuery.jointSeed root visit recognition)
  (SourceHistoryCommon.seed (paidExposure root visit recognition) (fullExposure root visit recognition))
def material := (Action.material root visit recognition, JointQuery.material root visit recognition,
  paidResult root visit recognition, Action.fullTrace root visit recognition, stock root visit recognition)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
