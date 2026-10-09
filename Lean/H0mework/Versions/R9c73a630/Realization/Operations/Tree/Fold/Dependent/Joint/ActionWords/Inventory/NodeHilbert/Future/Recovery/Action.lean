import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery
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

local instance : Module ℤ (JointCarrier root recognition visit successor transition alignment U7 calculus count) :=
  AddCommGroup.toIntModule _
def encode (letter : Letter root recognition visit successor) : Alphabet root recognition visit successor :=
  Classical.choose (decode_surjective root recognition visit successor letter)
theorem decode_encode (letter : Letter root recognition visit successor) :
    decode root recognition visit successor (encode root recognition visit successor letter)=letter :=
  Classical.choose_spec (decode_surjective root recognition visit successor letter)

abbrev coarseAdvance (first : Letter root recognition visit successor) :=
  SourceGeneratedActionWords.advance
    (actions root recognition visit successor transition alignment U7 calculus count)
    (coarseRead root recognition visit successor transition alignment U7 calculus count)
    (.simultaneous : Letter root recognition visit successor) first

theorem coarse_action (first : Letter root recognition visit successor)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    coarseRestriction root recognition visit successor transition alignment U7 calculus count
      (advance root recognition visit successor transition alignment U7 calculus count first value)=
    coarseAdvance root recognition visit successor transition alignment U7 calculus count first
      (coarseRestriction root recognition visit successor transition alignment U7 calculus count value) := by
  refine Submodule.Quotient.induction_on _ value (fun point => ?_)
  change coarseRestriction root recognition visit successor transition alignment U7 calculus count
    (advance root recognition visit successor transition alignment U7 calculus count first (projection root recognition visit successor transition alignment U7 calculus count point))=
      coarseAdvance root recognition visit successor transition alignment U7 calculus count first (coarseRestriction root recognition visit successor transition alignment U7 calculus count (projection root recognition visit successor transition alignment U7 calculus count point))
  rw [SourceGeneratedActionWords.advance_source,coarse_source,coarse_source]
  exact (SourceGeneratedActionWords.advance_source _ _ _ _ point).symm

def productAdvance (first : Letter root recognition visit successor) :
    JointCarrier root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ] JointCarrier root recognition visit successor transition alignment U7 calculus count :=
  ((coarseAdvance root recognition visit successor transition alignment U7 calculus count first).toAddMonoidHom.prodMap
    (wholeAdvance root recognition visit successor transition alignment U7 calculus count (encode root recognition visit successor first)).toAddMonoidHom).toIntLinearMap

theorem product_source (first : Letter root recognition visit successor)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    productAdvance root recognition visit successor transition alignment U7 calculus count first
      (together root recognition visit successor transition alignment U7 calculus count value)=
    together root recognition visit successor transition alignment U7 calculus count
      (advance root recognition visit successor transition alignment U7 calculus count first value) := by
  apply Prod.ext
  · exact (coarse_action root recognition visit successor transition alignment U7 calculus count first value).symm
  · have square := whole_advance_source root recognition visit successor transition alignment U7 calculus count (encode root recognition visit successor first) value
    exact square.trans (congrArg (fun letter => sourceMap root recognition visit successor transition alignment U7 calculus count (advance root recognition visit successor transition alignment U7 calculus count letter value))
      (decode_encode root recognition visit successor first))

def rangeAdvance (first : Letter root recognition visit successor) :
    Range root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ]
    Range root recognition visit successor transition alignment U7 calculus count :=
  ((productAdvance root recognition visit successor transition alignment U7 calculus count first).comp
    (together root recognition visit successor transition alignment U7 calculus count).range.subtype).codRestrict
    (Range root recognition visit successor transition alignment U7 calculus count) (by
      intro value
      obtain ⟨point,same⟩ := value.property
      change productAdvance root recognition visit successor transition alignment U7 calculus count first value.val ∈ _
      rw [← same,product_source]
      exact LinearMap.mem_range_self _ _)

theorem range_source (first : Letter root recognition visit successor)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    rangeAdvance root recognition visit successor transition alignment U7 calculus count first
      (emit root recognition visit successor transition alignment U7 calculus count value)=
    emit root recognition visit successor transition alignment U7 calculus count
      (advance root recognition visit successor transition alignment U7 calculus count first value) := by
  apply Subtype.ext
  exact product_source root recognition visit successor transition alignment U7 calculus count first value

theorem recover_action (first : Letter root recognition visit successor)
    (value : Range root recognition visit successor transition alignment U7 calculus count) :
    recover root recognition visit successor transition alignment U7 calculus count
      (rangeAdvance root recognition visit successor transition alignment U7 calculus count first value)=
    advance root recognition visit successor transition alignment U7 calculus count first
      (recover root recognition visit successor transition alignment U7 calculus count value) := by
  have source := range_source root recognition visit successor transition alignment U7 calculus count first (recover root recognition visit successor transition alignment U7 calculus count value)
  have read := congrArg (recover root recognition visit successor transition alignment U7 calculus count) source
  have left := congrArg (fun value => recover root recognition visit successor transition alignment U7 calculus count (rangeAdvance root recognition visit successor transition alignment U7 calculus count first value))
    (emit_recover root recognition visit successor transition alignment U7 calculus count value)
  exact left.symm.trans (read.trans (recover_emit root recognition visit successor transition alignment U7 calculus count
    (advance root recognition visit successor transition alignment U7 calculus count first (recover root recognition visit successor transition alignment U7 calculus count value))))

theorem recover_word (letters : List (Letter root recognition visit successor))
    (value : Range root recognition visit successor transition alignment U7 calculus count) :
    recover root recognition visit successor transition alignment U7 calculus count
      (SourceGeneratedActionWords.run (R:=ℤ) (rangeAdvance root recognition visit successor transition alignment U7 calculus count) letters value)=
    SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count)
      letters
      (recover root recognition visit successor transition alignment U7 calculus count value) := by
  induction letters generalizing value with
  | nil => rfl
  | cons first rest previous =>
      change recover root recognition visit successor transition alignment U7 calculus count
        (SourceGeneratedActionWords.run _ rest (rangeAdvance root recognition visit successor transition alignment U7 calculus count first value))=_
      exact (previous (rangeAdvance root recognition visit successor transition alignment U7 calculus count first value)).trans
        (congrArg (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) rest)
          (recover_action root recognition visit successor transition alignment U7 calculus count first value))

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
