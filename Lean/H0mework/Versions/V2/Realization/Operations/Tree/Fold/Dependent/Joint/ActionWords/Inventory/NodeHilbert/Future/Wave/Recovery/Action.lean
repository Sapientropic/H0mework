import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Recovery.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

def productAdvance (letter : Letter root recognition visit successor) :
    JointCarrier root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ] JointCarrier root recognition visit successor transition alignment U7 calculus count :=
  ((Inventory.advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom.prodMap
    ((PaidSourceFullOrbit.coherentAdvance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom.prodMap
      (Recovery.coarseAdvance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom)).toIntLinearMap
theorem product_source (letter : Letter root recognition visit successor)
    (value : Original root recognition visit successor transition alignment U7 calculus count) :
    productAdvance root recognition visit successor transition alignment U7 calculus count letter
      (together root recognition visit successor transition alignment U7 calculus count value)=
      together root recognition visit successor transition alignment U7 calculus count
        (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact PaidSourceFullOrbit.coherent_source root recognition visit successor transition alignment U7 calculus count letter value
    · rfl
def rangeAdvance (letter : Letter root recognition visit successor) :
    Range root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ] Range root recognition visit successor transition alignment U7 calculus count :=
  GeneratedRangeAction.advance (together root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom
    (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom
    (productAdvance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom
    (product_source root recognition visit successor transition alignment U7 calculus count letter)
theorem range_source (letter : Letter root recognition visit successor)
    (value : Original root recognition visit successor transition alignment U7 calculus count) :
    rangeAdvance root recognition visit successor transition alignment U7 calculus count letter
      (emit root recognition visit successor transition alignment U7 calculus count value)=
      emit root recognition visit successor transition alignment U7 calculus count
        (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value) := by
  apply Subtype.ext
  exact product_source root recognition visit successor transition alignment U7 calculus count letter value
theorem recover_action (first : Letter root recognition visit successor)
    (value : Range root recognition visit successor transition alignment U7 calculus count) :
    recover root recognition visit successor transition alignment U7 calculus count
      (rangeAdvance root recognition visit successor transition alignment U7 calculus count first value)=
    PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count first
      (recover root recognition visit successor transition alignment U7 calculus count value) := by
  have source := range_source root recognition visit successor transition alignment U7 calculus count first (recover root recognition visit successor transition alignment U7 calculus count value)
  have read := congrArg (recover root recognition visit successor transition alignment U7 calculus count) source
  have left := congrArg (fun value => recover root recognition visit successor transition alignment U7 calculus count (rangeAdvance root recognition visit successor transition alignment U7 calculus count first value))
    (emit_recover root recognition visit successor transition alignment U7 calculus count value)
  exact left.symm.trans (read.trans (recover_emit root recognition visit successor transition alignment U7 calculus count
    (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count first (recover root recognition visit successor transition alignment U7 calculus count value))))

theorem recover_word (letters : List (Letter root recognition visit successor))
    (value : Range root recognition visit successor transition alignment U7 calculus count) :
    recover root recognition visit successor transition alignment U7 calculus count
      (SourceGeneratedActionWords.run (R:=ℤ) (rangeAdvance root recognition visit successor transition alignment U7 calculus count) letters value)=
    SourceGeneratedActionWords.run (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count)
      letters
      (recover root recognition visit successor transition alignment U7 calculus count value) := by
  induction letters generalizing value with
  | nil => rfl
  | cons first rest previous =>
      change recover root recognition visit successor transition alignment U7 calculus count
        (SourceGeneratedActionWords.run _ rest (rangeAdvance root recognition visit successor transition alignment U7 calculus count first value))=_
      exact (previous (rangeAdvance root recognition visit successor transition alignment U7 calculus count first value)).trans
        (congrArg (SourceGeneratedActionWords.run (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count) rest)
          (recover_action root recognition visit successor transition alignment U7 calculus count first value))

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
