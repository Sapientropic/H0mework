import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Runtime
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request
open RootInquiryCompletion RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (count : Nat)
theorem kernel_word_read (sound : GeneratedRelationSoundnessAt (face root visit recognition count))
    (coordinate : GeneratedKernelResidualCoordinateAt (face root visit recognition count) sound) :
    (combined root visit recognition count).completionProjection (kernelWord root visit recognition count sound coordinate) =
      coordinate.coordinate.val :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective (combined root visit recognition count).relationInGeneratorClosure
    coordinate.coordinate.val)

theorem kernel_word_value (sound : GeneratedRelationSoundnessAt (face root visit recognition count))
    (coordinate : GeneratedKernelResidualCoordinateAt (face root visit recognition count) sound) :
    SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result) (mixed root visit recognition)
      (kernelWord root visit recognition count sound coordinate).val = 0 := by
  have generated := congrArg ((face root visit recognition count).completionEvaluation sound)
    (kernel_word_read root visit recognition count sound coordinate)
  change (face root visit recognition count).freeEvaluation (kernelWord root visit recognition count sound coordinate).val =
      (face root visit recognition count).completionEvaluation sound coordinate.coordinate.val at generated
  exact (word_read root visit recognition count _).symm.trans
    (generated.trans coordinate.maps_to_zero)

theorem coverage_word_value (sound : GeneratedRelationSoundnessAt (face root visit recognition count))
    (coordinate : GeneratedCoverageResidualCoordinateAt (face root visit recognition count) sound) :
    SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result)
      (mixed root visit recognition) (coverageWord root visit recognition count sound coordinate) = coordinate.representative := by
  simp only [coverageWord,SourceOperationScalarRelations.evaluation,Finsupp.linearCombination_single,
    one_smul,SourceOperationEffects.Expr.eval]

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (word : Word root visit recognition)
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (root visit activated_query activated_answer activated_next)
end M

def materialFace (stage : Nat) : SourceNativeRootSemanticFaceAt
    (M.root (requestRoot root visit recognition count word) (queryVisit root visit recognition count)
      (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
      (requestReader root visit recognition count word) stage)
    (M.visit (requestRoot root visit recognition count word) (queryVisit root visit recognition count)
      (requestReader root visit recognition count word) stage) where
  projection := .inherited (.inherited (.inherited
    ((RootGeneratedDebtActivationJointSource.OwnerFree.baseInstallation
      (requestRoot root visit recognition count word).toAuthoritativeRoot
        (queryVisit root visit recognition count).current (requestReader root visit recognition count word)).embed
          (.inl (.component PUnit.unit)))))
  active := PUnit.unit
  classifier_eq := rfl

theorem word_material (stage : Nat) :
    (materialFace root visit recognition count U7 calculus word stage).rootRead.2.1 = word := rfl

theorem original_disposition (stage : Nat) :
    (materialFace root visit recognition count U7 calculus word stage).rootRead.1 =
      disposition root visit recognition count := rfl

theorem original_paid_state (stage : Nat) :
    (materialFace root visit recognition count U7 calculus word stage).rootRead.2.2.2.2 =
      RootGeneratedDebtActivationJointSource.OwnerFree.runtimeCurrent (actualRoot root visit recognition).toAuthoritativeRoot
        visit.current (installedReader root visit recognition) (paidRuntime root visit recognition count) := rfl

theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (requestRoot root visit recognition count word) (queryVisit root visit recognition count)
      (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
      (requestReader root visit recognition count word) offset) ∧
    type_of% (M.activated_answer (requestRoot root visit recognition count word) (queryVisit root visit recognition count)
      (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
      (requestReader root visit recognition count word) offset) ∧
    type_of% (M.activated_next (requestRoot root visit recognition count word) (queryVisit root visit recognition count)
      (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
      (requestReader root visit recognition count word) offset) :=
  ⟨M.activated_query _ _ _ _ _ _,M.activated_answer _ _ _ _ _ _,M.activated_next _ _ _ _ _ _⟩

namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value trace value_source paid_history)
end O

theorem normal : O.value (requestRoot root visit recognition count word).toAuthoritativeRoot
    (queryVisit root visit recognition count).current (requestReader root visit recognition count word) =
    SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=SourceOperationNative.Tree.Fold.Slot.result)
      (mixed root visit recognition) word :=
  (O.value_source _ _ _).trans (SourceOperationExecution.Coefficients.expression_eval _ _)

theorem cost : (O.trace (requestRoot root visit recognition count word).toAuthoritativeRoot
    (queryVisit root visit recognition count).current (requestReader root visit recognition count word)).length =
      SourceOperationExecution.Coefficients.cost word :=
  (O.paid_history _ _ _).trans (SourceOperationExecution.Coefficients.expression_remaining _)
theorem whole_next (stage : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (requestRoot root visit recognition count word).toAuthoritativeRoot
        (queryVisit root visit recognition count).current (requestReader root visit recognition count word) stage) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next _ _ _ _

theorem no_refill (stage : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.no_refill
      (requestRoot root visit recognition count word).toAuthoritativeRoot
        (queryVisit root visit recognition count).current (requestReader root visit recognition count word) stage) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.no_refill _ _ _ _

theorem wellFounded : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.wellFounded
      (requestRoot root visit recognition count word).toAuthoritativeRoot
        (queryVisit root visit recognition count).current (requestReader root visit recognition count word)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.wellFounded _ _ _
end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
