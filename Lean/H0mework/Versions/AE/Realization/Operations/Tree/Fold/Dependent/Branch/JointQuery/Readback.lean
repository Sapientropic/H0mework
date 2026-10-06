import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Installation
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
open RootInquiryCompletion RootLawDependentJointStateController
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
def sourceFace : SourceNativeRootSemanticFaceAt (sourceRoot root visit recognition) visit where
 projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface (Branch.actualRoot root visit recognition).source.base
 (component root visit recognition)).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
theorem complete_material : (sourceFace root visit recognition).rootRead=material root visit recognition := rfl
theorem exact_source_ledger : (sourceRoot root visit recognition).toAuthoritativeRoot.toLedgerRoot=root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem installed_raw : installedReader root visit recognition (root.emitted visit.current)=raw root visit recognition := rfl
theorem paid_core : (batchResult root visit recognition).2.2.1 0=(coreResult root visit recognition).2.2.1 :=
 ((congrArg (fun values : Value root visit recognition .result => values 0)
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _)).trans
 (query_core root visit recognition)).trans
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).symm
theorem paid_relation : (batchResult root visit recognition).2.2.1 1=
 ((Relation.relationExpression root visit recognition).eval (Relation.mixed root visit recognition),
 (Relation.relationExpression root visit recognition).effect (Relation.mixed root visit recognition) (increment root visit recognition)) :=
 (congrArg (fun values : Value root visit recognition .result => values 1)
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _)).trans (query_relation root visit recognition)
theorem exact_fee : (batchResult root visit recognition).2.1.2.length=
 remaining (coreTerm root visit recognition)+remaining (relationTerm root visit recognition)+4 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans (query_charge root visit recognition)
theorem mapped_core_preserved (event) (present : event ∈ (coreWritten root visit recognition).trace) :
 event ∈ (jointSeed root visit recognition).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event ((SourceHistoryCommon.parallel_right _ _ _).1 event
 ((SourceHistoryCommon.parallel_left _ _ _).1 event present))
theorem mapped_relation_preserved (event) (present : event ∈ (relationWritten root visit recognition).trace) :
 event ∈ (jointSeed root visit recognition).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event ((SourceHistoryCommon.parallel_right _ _ _).1 event
 ((SourceHistoryCommon.parallel_right _ _ _).1 event present))
theorem batch_preserved (event) (present : event ∈ (SourceOperationPaidRelations.exposure (batchResult root visit recognition).2.1.2).trace) :
 event ∈ (jointSeed root visit recognition).trace := (SourceHistoryCommon.parallel_right _ _ _).1 event present
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem initial_inventory : (initial root visit recognition U7 calculus).inventory=some (jointSeed root visit recognition) := rfl
theorem initial_source : (initial root visit recognition U7 calculus).old=(fixedFrame root visit recognition U7 calculus).old ∧
 (initial root visit recognition U7 calculus).registered=(fixedFrame root visit recognition U7 calculus).registered := ⟨rfl,rfl⟩
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
