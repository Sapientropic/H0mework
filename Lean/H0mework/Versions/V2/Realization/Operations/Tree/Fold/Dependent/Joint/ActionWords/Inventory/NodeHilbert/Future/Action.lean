import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Kernel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
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

def shift (bound : Nat) (first : Alphabet root recognition visit successor) :
    Space root recognition visit successor (bound+1) →ₗ[ℤ] Space root recognition visit successor bound :=
  (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H)).symm.toLinearMap.comp
    ((LinearMap.pi (fun cell => LinearMap.proj (prepend root recognition visit successor bound first cell.1,cell.2))).comp
      (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor (bound+1) → H)).toLinearMap)
theorem shift_source (bound : Nat) (first : Alphabet root recognition visit successor)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    shift root recognition visit successor bound first
      (observation root recognition visit successor transition alignment U7 calculus count (bound+1) value) =
    observation root recognition visit successor transition alignment U7 calculus count bound
      (advance root recognition visit successor transition alignment U7 calculus count (decode root recognition visit successor first) value) := by
  apply (WithLp.linearEquiv 2 ℤ (Cells root recognition visit successor bound → H)).injective
  funext cell
  change Covariance.feature root recognition visit successor transition alignment U7 calculus count
      (actor root recognition visit successor cell.2)
      (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count)
        (word root recognition visit successor (prepend root recognition visit successor bound first cell.1)) value) = _
  rw [prepend_word]
  rfl

theorem shift_restriction (bound : Nat) (first : Alphabet root recognition visit successor) :
    (shift root recognition visit successor bound first).comp (restriction root recognition visit successor (bound+1)) =
      (restriction root recognition visit successor bound).comp (shift root recognition visit successor (bound+1) first) := rfl

def historyMorphism (first : Alphabet root recognition visit successor) : SourceGeneratedScalarCofinalNaturality.Morphism
    (SourceGeneratedScalarCofinalTail.tail (data root recognition visit successor transition alignment U7 calculus count))
    (data root recognition visit successor transition alignment U7 calculus count) where
  generatorMap := advance root recognition visit successor transition alignment U7 calculus count (decode root recognition visit successor first)
  stageMap := fun bound => shift root recognition visit successor bound first
  transition_naturality := fun bound => (shift_restriction root recognition visit successor bound first).symm
  evaluator_naturality := fun bound => by
    apply LinearMap.ext
    exact shift_source root recognition visit successor transition alignment U7 calculus count bound first

abbrev wholeAdvance (first : Alphabet root recognition visit successor) :=
  ((historyMorphism root recognition visit successor transition alignment U7 calculus count first).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible
      (data root recognition visit successor transition alignment U7 calculus count)
      (compatible root recognition visit successor transition alignment U7 calculus count))
    (compatible root recognition visit successor transition alignment U7 calculus count)).hom.comp
      (SourceGeneratedScalarCofinalTail.completionMap
        (data root recognition visit successor transition alignment U7 calculus count)
        (compatible root recognition visit successor transition alignment U7 calculus count)).hom

theorem whole_advance_source (first : Alphabet root recognition visit successor)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    wholeAdvance root recognition visit successor transition alignment U7 calculus count first
      (sourceMap root recognition visit successor transition alignment U7 calculus count value) =
    sourceMap root recognition visit successor transition alignment U7 calculus count
      (advance root recognition visit successor transition alignment U7 calculus count (decode root recognition visit successor first) value) := by
  have tail := CategoryTheory.ConcreteCategory.congr_hom
    (SourceGeneratedScalarCofinalTail.completionMap_source
      (data root recognition visit successor transition alignment U7 calculus count)
      (compatible root recognition visit successor transition alignment U7 calculus count)) value
  have source := CategoryTheory.ConcreteCategory.congr_hom
    ((historyMorphism root recognition visit successor transition alignment U7 calculus count first).completionMorphism_source_naturality
      (SourceGeneratedScalarCofinalTail.compatible
        (data root recognition visit successor transition alignment U7 calculus count)
        (compatible root recognition visit successor transition alignment U7 calculus count))
      (compatible root recognition visit successor transition alignment U7 calculus count)) value
  exact (congrArg ((historyMorphism root recognition visit successor transition alignment U7 calculus count first).completionMorphism
    (SourceGeneratedScalarCofinalTail.compatible
      (data root recognition visit successor transition alignment U7 calculus count)
      (compatible root recognition visit successor transition alignment U7 calculus count))
    (compatible root recognition visit successor transition alignment U7 calculus count)).hom tail).trans source

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
