import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Consumer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Relations.Consumer
/-! The original Branch relation calculation exports its paid relation histories and exact disposition. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation
open RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
namespace R
export RootGeneratedDebtActivationJointSource.OwnerFree.Relations
  (atPrefix endpoint history evaluationFace relations_sound coversAt_factorizes tick_equation_and_whole_next boundary_in_inventory)
end R
abbrev paidRelationPrefixes := R.atPrefix (actualRoot root visit recognition).toAuthoritativeRoot
  visit.current (installedReader root visit recognition)
abbrev paidRelationEndpoint := R.endpoint (actualRoot root visit recognition).toAuthoritativeRoot
  visit.current (installedReader root visit recognition)

def paidRuntime (count : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime
  (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition) count
abbrev paidRelationHistory (count : Nat) := R.history (actualRoot root visit recognition).toAuthoritativeRoot
  visit.current (installedReader root visit recognition) (paidRuntime root visit recognition count)

theorem paid_relation_closure_sound (count : Nat) :
    (R.evaluationFace (actualRoot root visit recognition).toAuthoritativeRoot visit.current
      (installedReader root visit recognition) (paidRuntime root visit recognition count)).RelationsSound :=
  R.relations_sound _ _ _ _

theorem paid_relation_whole_next (count : Nat) : type_of% (R.coversAt_factorizes
    (actualRoot root visit recognition).toAuthoritativeRoot visit.current
      (installedReader root visit recognition) (paidRuntime root visit recognition count)) :=
  R.coversAt_factorizes _ _ _ _

theorem actual_paid_boundary (count : Nat) : type_of% (R.boundary_in_inventory
    (actualRoot root visit recognition).toAuthoritativeRoot visit.current
      (installedReader root visit recognition) (paidRuntime root visit recognition count)) :=
  R.boundary_in_inventory _ _ _ _
end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
