import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Installation
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment

/-! All source-generated tree stages retain complete material and pay the
same calculation debt through the existing whole-ledger and Noetherian law. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Installation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
variable {Root Carrier : Type u}
variable (atOccurrence : Root → List Carrier → Carrier)
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (source : {current : V.Current} → (occurrence : Occurrence old current) → TreeReadAt (Root:=Root) old occurrence)
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment
  (activePayment debtCurrent budget wellFounded endpoint_budget)
end P
abbrev actualReader := fun (_ : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  old.visit.current) => reader atOccurrence old source (old.root.emitted old.visit.current)
def payment (count : Fin (Fold.budget (treeAt old source (old.root.emitted old.visit.current)))) :=
  P.activePayment old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source)
    ⟨count.1, by
      change count.1 < remaining (program atOccurrence (treeAt old source (old.root.emitted old.visit.current)))
      rw [program_budget]
      exact count.2⟩
theorem actual_budget (count : Nat) :
    (P.debtCurrent old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source) count).budget =
      budget (treeAt old source (old.root.emitted old.visit.current)) - count :=
  (P.budget old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source) count).trans
    (congrArg (fun value => value - count) (program_budget _ _))
abbrev sourceSeed := RootGeneratedDebtActivationJointSource.OwnerFree.initialRuntime
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source)
abbrev sourceRoot := RootGeneratedDebtActivationJointSource.OwnerFree.authoritativeRoot
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source)
abbrev stageMaterial (count : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
    (sourceRoot atOccurrence old source)
    ((sourceRoot atOccurrence old source).emitted
      (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
        old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source) count))
theorem source_whole (count : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.destination_entry
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.destination_entry
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source) count

abbrev completedTrace := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source)

theorem completed_cost : (completedTrace atOccurrence old source).length =
    Fold.budget (treeAt old source (old.root.emitted old.visit.current)) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source)).trans
      (program_budget _ _)

theorem query_charged_history : (I.resultFace old (reader atOccurrence old source)).rootRead.2.1.2 =
    completedTrace atOccurrence old source := rfl

theorem query_original_material : (I.resultFace old (reader atOccurrence old source)).rootRead.2.2.2 =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      old.root.toAuthoritativeRoot (old.root.emitted old.visit.current) := rfl

theorem no_refill (count : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.no_refill
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.no_refill
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source) count

theorem same_debt_wellFounded : type_of% (P.wellFounded
    old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source)) :=
  P.wellFounded old.root.toAuthoritativeRoot old.visit.current (actualReader atOccurrence old source)

end SourceOperationNative.Tree.Fold.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
