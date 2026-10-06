import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Relations.Source
/-! Complete paid-prefix equations consume the same occurrence, whole ledger and canonical next. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Relations
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
open RootInquiryCompletion CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))
variable (runtime : Runtime old origin reader)
theorem actual_state : current old origin reader runtime = runtimeCurrent old origin reader runtime := rfl

theorem complete_paid_events : exposure old origin reader runtime =
    SourceOperationPaidRelations.exposure (runtimeCurrent old origin reader runtime).2 := rfl

theorem paid_steps : (SourceOperationPaidRelations.words (current old origin reader runtime).2).length =
    (runtimeCurrent old origin reader runtime).2.length :=
  SourceOperationPaidRelations.complete_steps _

theorem word_read (word : Expr Value Var sort →₀ ℤ) :
    (evaluationFace old origin reader runtime).freeEvaluation word =
      evaluation (R:=ℤ) (raw old origin reader).environment word :=
  SourceOperationPaidRelations.word_read _ (runtimeCurrent old origin reader runtime).2 word

theorem relations_sound : (evaluationFace old origin reader runtime).RelationsSound :=
  SourceOperationPaidRelations.relations_sound _ (runtimeCurrent old origin reader runtime).2

theorem step_in_inventory (word : Expr Value Var sort →₀ ℤ)
    (belongs : word ∈ SourceOperationPaidRelations.words (runtimeCurrent old origin reader runtime).2) :
    word ∈ (history old origin reader runtime).relationClosure :=
  SourceOperationPaidRelations.step_in_inventory _ _ word belongs

theorem boundary_in_inventory : relationMap (R:=ℤ) (raw old origin reader).environment
    (runtimeCurrent old origin reader runtime).2.relationWords ∈
      (history old origin reader runtime).relationClosure :=
  SourceOperationPaidRelations.boundary_in_inventory _ (runtimeCurrent old origin reader runtime).2

theorem coversAt_factorizes : type_of% ((facade old origin reader).readoutAt_factorizes runtime
    ((baseInstallation old origin reader).embed (.inr (.inr PUnit.unit)))) :=
  (facade old origin reader).readoutAt_factorizes runtime
    ((baseInstallation old origin reader).embed (.inr (.inr PUnit.unit)))

theorem tick_equation_and_whole_next :
    (evaluationFace old origin reader runtime).RelationsSound ∧
    type_of% (coversAt_factorizes old origin reader runtime) :=
  ⟨relations_sound old origin reader runtime,coversAt_factorizes old origin reader runtime⟩
end RootGeneratedDebtActivationJointSource.OwnerFree.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
