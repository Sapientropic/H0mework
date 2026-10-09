import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation
open RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarCochain
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
theorem generated_relation_zero : evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result) (mixed root visit recognition) (relationWord root visit recognition) = 0 :=
  evaluation_updateWord _ _ _

theorem compiled_relation_zero : (relationExpression root visit recognition).eval (mixed root visit recognition) = 0 :=
  (SourceOperationExecution.Coefficients.expression_eval _ _).trans (generated_relation_zero root visit recognition)

namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment no_refill wellFounded)
end P

theorem normal : O.value root.toAuthoritativeRoot visit.current (installedReader root visit recognition) = 0 :=
  (O.value_source root.toAuthoritativeRoot visit.current (installedReader root visit recognition)).trans
    (compiled_relation_zero root visit recognition)

theorem cost : (O.trace root.toAuthoritativeRoot visit.current (installedReader root visit recognition)).length =
    SourceOperationExecution.Coefficients.cost (relationWord root visit recognition) :=
  (O.paid_history root.toAuthoritativeRoot visit.current (installedReader root visit recognition)).trans
    (SourceOperationExecution.Coefficients.expression_remaining (relationWord root visit recognition))

theorem boundary_source : SourceOperationCochain.boundary
    (Finsupp.single (programme root visit recognition) (1 : ℤ)) = relationWord root visit recognition := by
  exact (SourceOperationCochain.boundary_single _ _).trans (one_smul _ _)

theorem cochain_first : type_of% (SourceOperationCochain.cochain_d₀ (s:=SourceOperationNative.Tree.Fold.Slot.result)
    (environment root visit recognition) (delta root visit recognition)) :=
  SourceOperationCochain.cochain_d₀ (s:=SourceOperationNative.Tree.Fold.Slot.result) (environment root visit recognition) (delta root visit recognition)

theorem cochain_second : type_of% (SourceOperationCochain.cochain_d₁ (s:=SourceOperationNative.Tree.Fold.Slot.result)
    (environment root visit recognition) (delta root visit recognition)) :=
  SourceOperationCochain.cochain_d₁ (s:=SourceOperationNative.Tree.Fold.Slot.result) (environment root visit recognition) (delta root visit recognition)

theorem cochain_relation_zero (word : ScalarRelationPresentation.PresentedCarrier ℤ
    ((complex root visit recognition).X 0)) :
    ScalarRelationPresentation.presentedEquiv (R:=ℤ) ((complex root visit recognition).X 2)
      (ScalarRelationPresentation.presentedMap ((complex root visit recognition).d 1 2).hom
        (ScalarRelationPresentation.presentedMap ((complex root visit recognition).d 0 1).hom word)) = 0 :=
  SourceOperationCochain.cochain_presented_comp_zero (environment root visit recognition) (delta root visit recognition) word

theorem no_refill (count : Nat) : type_of% (P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition) count) :=
  P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition) count

theorem wellFounded : type_of% (P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition)) :=
  P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition)

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem word_material (count : Nat) : (materialFace root visit recognition U7 calculus count).rootRead.2.2.1 = relationWord root visit recognition := rfl

theorem programme_material (count : Nat) : (materialFace root visit recognition U7 calculus count).rootRead.2.1 = programme root visit recognition := rfl

theorem parent_next (count : Nat) : type_of% (SourceTemporalMaterial.Calculation.parent_next_preserved
    (sourceRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) count) :=
  SourceTemporalMaterial.Calculation.parent_next_preserved
    (sourceRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) count

theorem whole_next (count : Nat) : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition) count
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end M
theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset) ∧
    type_of% (M.activated_answer (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset) ∧
    type_of% (M.activated_next (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset) :=
  ⟨M.activated_query (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset,
    M.activated_answer (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset,
    M.activated_next (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition) offset⟩
end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
