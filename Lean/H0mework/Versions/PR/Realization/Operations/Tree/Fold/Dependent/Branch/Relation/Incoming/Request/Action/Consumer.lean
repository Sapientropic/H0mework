import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action
open RootInquiryCompletion RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (count : Nat)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (word : Word root visit recognition)
def materialFace (stage : Nat) : SourceNativeRootSemanticFaceAt
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.root
      (sourceRoot root visit recognition count word) (queryVisit root visit recognition count)
      (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
      (reader root visit recognition count word) stage)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.visit
      (sourceRoot root visit recognition count word) (queryVisit root visit recognition count)
      (reader root visit recognition count word) stage) where
  projection := .inherited (.inherited (.inherited
    ((RootGeneratedDebtActivationJointSource.OwnerFree.baseInstallation
      (sourceRoot root visit recognition count word).toAuthoritativeRoot
      (queryVisit root visit recognition count).current (reader root visit recognition count word)).embed
        (.inl (.component PUnit.unit)))))
  active := PUnit.unit
  classifier_eq := rfl

theorem original_word (stage : Nat) : (materialFace root visit recognition count U7 calculus word stage).rootRead.2.1 = word := rfl

theorem actual_word (stage : Nat) : (materialFace root visit recognition count U7 calculus word stage).rootRead.1.2.1 =
    acted root visit recognition word := rfl

theorem original_actor (stage : Nat) : (materialFace root visit recognition count U7 calculus word stage).rootRead.2.2 =
    Branch.Relation.Action.material root visit recognition := rfl

theorem actual_value : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
    (sourceRoot root visit recognition count word).toAuthoritativeRoot
    (queryVisit root visit recognition count).current (reader root visit recognition count word) =
      SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result)
        (Branch.Relation.Action.environment root visit recognition) word :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    ((SourceOperationExecution.Coefficients.expression_eval _ _).trans
      (Branch.Relation.Action.word_equation root visit recognition word))

theorem actual_cost : (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace
    (sourceRoot root visit recognition count word).toAuthoritativeRoot
    (queryVisit root visit recognition count).current (reader root visit recognition count word)).length =
      SourceOperationExecution.Coefficients.cost (acted root visit recognition word) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history _ _ _).trans
    (SourceOperationExecution.Coefficients.expression_remaining _)

theorem actual_whole_next (stage : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (sourceRoot root visit recognition count word).toAuthoritativeRoot
    (queryVisit root visit recognition count).current (reader root visit recognition count word) stage) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next _ _ _ _

theorem actual_no_refill (stage : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.no_refill
    (sourceRoot root visit recognition count word).toAuthoritativeRoot
    (queryVisit root visit recognition count).current (reader root visit recognition count word) stage) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.no_refill _ _ _ _

theorem actual_noetherian : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.wellFounded
    (sourceRoot root visit recognition count word).toAuthoritativeRoot
    (queryVisit root visit recognition count).current (reader root visit recognition count word)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.wellFounded _ _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
