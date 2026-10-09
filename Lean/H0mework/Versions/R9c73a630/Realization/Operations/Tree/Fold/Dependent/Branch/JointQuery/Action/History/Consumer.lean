import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Action.History.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Action.Consumer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState

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

theorem literal_old_stock (event) (present : event ∈ (JointQuery.jointSeed root visit recognition).trace) :
    event ∈ (stock root visit recognition).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem actual_paid_preserved (event) (present : event ∈ (paidExposure root visit recognition).trace) :
    event ∈ (stock root visit recognition).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event
    ((SourceHistoryCommon.parallel_left _ _ _).1 event present)

theorem full_trace_preserved (event) (present : event ∈ (fullExposure root visit recognition).trace) :
    event ∈ (stock root visit recognition).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event
    ((SourceHistoryCommon.parallel_right _ _ _).1 event present)

theorem same_raw_exposure : paidExposure root visit recognition =
    SourceOperationPaidRelations.exposure (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
      (JointQuery.sourceRoot root visit recognition).toAuthoritativeRoot visit.current
        (fun _ => Action.raw root visit recognition)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure root.toAuthoritativeRoot visit.current
    (JointQuery.sourceRoot root visit recognition).toAuthoritativeRoot visit.current (Action.raw root visit recognition)

theorem source_raw : (paidResult root visit recognition).1 = Action.raw root visit recognition := rfl

theorem source_material : (paidResult root visit recognition).2.2.2 =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      root.toAuthoritativeRoot (root.emitted visit.current) := rfl

theorem source_action : (material root visit recognition).1.1 = Relation.Action.material root visit recognition := rfl

theorem paid_full_fee : (paidResult root visit recognition).2.1.2.length =
    (Action.fullTrace root visit recognition).length :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
    (Action.full_trace_charge root visit recognition).symm

theorem complete_fee : (paidResult root visit recognition).2.1.2.length =
    remaining (Branch.raw root visit recognition).expression +
      SourceOperationExecution.Coefficients.cost (Relation.relationWord root visit recognition) + 4 :=
  (paid_full_fee root visit recognition).trans (Action.full_charge root visit recognition)

theorem paid_value : (paidResult root visit recognition).2.2.1 =
    (JointQuery.expression root visit recognition).eval (JointQuery.environment root visit recognition) +
      (JointQuery.expression root visit recognition).effect (JointQuery.environment root visit recognition)
        (Action.increment root visit recognition) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
    (Action.actual_update root visit recognition)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
