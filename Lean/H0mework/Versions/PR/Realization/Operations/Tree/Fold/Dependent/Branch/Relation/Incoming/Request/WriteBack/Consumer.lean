import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.WriteBack.Laws
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.WriteBack
open RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (count : Nat)
variable (sound : GeneratedRelationSoundnessAt (face root visit recognition count))
variable (coordinate : GeneratedKernelResidualCoordinateAt (face root visit recognition count) sound)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev dispositionAt (stage : Nat) := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.settleWithResidual
  (evaluationFace root visit recognition count sound coordinate stage)

def OutputAt (stage : Nat) (selected : ResidualDispositionOutcome
    (evaluationFace root visit recognition count sound coordinate stage)) : Type u :=
  match selected with
  | .faithful _ _ _ => (actualUpdated root visit recognition count sound coordinate stage).CompletionCarrier ≃+ Value root visit recognition SourceOperationNative.Tree.Fold.Slot.result
  | .unsound _ _ => GeneratedRelationResidualCoordinateAt (evaluationFace root visit recognition count sound coordinate stage)
  | .kernelResidual nextSound _ _ => GeneratedKernelResidualCoordinateAt (evaluationFace root visit recognition count sound coordinate stage) nextSound
  | .coverageResidual nextSound _ _ => GeneratedCoverageResidualCoordinateAt (evaluationFace root visit recognition count sound coordinate stage) nextSound

def outputAt (stage : Nat) : OutputAt root visit recognition count sound coordinate stage
    (dispositionAt root visit recognition count sound coordinate stage) := by
  generalize selectedEq : dispositionAt root visit recognition count sound coordinate stage = selected
  cases selected with
  | faithful nextSound coverage proof => exact proof.canonicalQuotientAddEquiv
  | unsound obstruction nextCoordinate => exact nextCoordinate
  | kernelResidual nextSound obstruction nextCoordinate => exact nextCoordinate
  | coverageResidual nextSound obstruction nextCoordinate => exact nextCoordinate
theorem source_factorizes (stage : Nat) : type_of%
    ((RootGeneratedDebtActivationJointSource.OwnerFree.facade
      (sourceRoot root visit recognition count sound coordinate).toAuthoritativeRoot
      (sourceVisit root visit recognition count sound coordinate).current
      (requestReader root visit recognition count (word root visit recognition count sound coordinate))).readoutAt_factorizes
        (actualRuntime root visit recognition count sound coordinate stage)
        (sourceInstalledFace root visit recognition count sound coordinate stage).projection) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.facade
    (sourceRoot root visit recognition count sound coordinate).toAuthoritativeRoot
    (sourceVisit root visit recognition count sound coordinate).current
    (requestReader root visit recognition count (word root visit recognition count sound coordinate))).readoutAt_factorizes _ _
theorem query_answer_next (offset : Nat) :
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_query
      (sourceRoot root visit recognition count sound coordinate) (sourceVisit root visit recognition count sound coordinate)
      (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
      (requestReader root visit recognition count (word root visit recognition count sound coordinate)) offset) ∧
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_answer
      (sourceRoot root visit recognition count sound coordinate) (sourceVisit root visit recognition count sound coordinate)
      (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
      (requestReader root visit recognition count (word root visit recognition count sound coordinate)) offset) ∧
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_next
      (sourceRoot root visit recognition count sound coordinate) (sourceVisit root visit recognition count sound coordinate)
      (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
      (requestReader root visit recognition count (word root visit recognition count sound coordinate)) offset) :=
  ⟨RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_query _ _ _ _ _ _,
   RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_answer _ _ _ _ _ _,
   RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_next _ _ _ _ _ _⟩

end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.WriteBack
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
