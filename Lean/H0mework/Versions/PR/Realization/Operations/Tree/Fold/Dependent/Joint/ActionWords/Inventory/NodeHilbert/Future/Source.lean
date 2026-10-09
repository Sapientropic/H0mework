import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words.Consumer
import Mathlib.Data.List.OfFn
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

abbrev Alphabet := Index root recognition visit successor ⊕ Unit
def decode : Alphabet root recognition visit successor → Letter root recognition visit successor
  | .inl node => match actor root recognition visit successor node with
      | .inl source => .source source
      | .inr target => .target target
  | .inr _ => .simultaneous
abbrev Code (bound : Nat) := Σ length : Fin (bound+1), Fin length.val → Alphabet root recognition visit successor
def word {bound : Nat} (code : Code root recognition visit successor bound) := (List.ofFn code.2).map (decode root recognition visit successor)
def lengthRestriction (bound : Nat) : Code root recognition visit successor bound → Code root recognition visit successor (bound+1)
  | ⟨length,letters⟩ => ⟨length.castSucc,letters⟩
theorem restriction_word (bound : Nat) (code : Code root recognition visit successor bound) :
    word root recognition visit successor (lengthRestriction root recognition visit successor bound code)=word root recognition visit successor code := rfl
theorem decode_surjective : Function.Surjective (decode root recognition visit successor) := by
  intro selected
  cases selected with
  | source source =>
    obtain ⟨index,same⟩ := List.mem_iff_get.mp source.property
    refine ⟨.inl (.inl index),?_⟩
    exact congrArg Letter.source (Subtype.ext same)
  | target target =>
    obtain ⟨index,same⟩ := List.mem_iff_get.mp target.property
    refine ⟨.inl (.inr index),?_⟩
    exact congrArg Letter.target (Subtype.ext same)
  | simultaneous => exact ⟨.inr (),rfl⟩
theorem code_words (letters : List (Letter root recognition visit successor)) :
    ∃ codes : List (Alphabet root recognition visit successor), codes.map (decode root recognition visit successor)=letters := by
  induction letters with
  | nil => exact ⟨[],rfl⟩
  | cons letter rest previous =>
    obtain ⟨code,same⟩ := decode_surjective root recognition visit successor letter
    obtain ⟨codes,remaining⟩ := previous
    exact ⟨code::codes,by simp only [List.map_cons,same,remaining]⟩
theorem word_coverage (bound : Nat) (letters : List (Letter root recognition visit successor)) (bounded : letters.length ≤ bound) :
    ∃ code : Code root recognition visit successor bound, word root recognition visit successor code=letters := by
  obtain ⟨codes,same⟩ := code_words root recognition visit successor letters
  have size : codes.length ≤ bound := by simpa only [← same,List.length_map] using bounded
  exact ⟨⟨⟨codes.length,Nat.lt_succ_of_le size⟩,codes.get⟩,by simpa only [word,List.ofFn_get] using same⟩

def prepend (bound : Nat) (first : Alphabet root recognition visit successor) :
    Code root recognition visit successor bound → Code root recognition visit successor (bound+1)
  | ⟨length,letters⟩ => ⟨length.succ,Fin.cases first letters⟩
theorem prepend_word (bound : Nat) (first : Alphabet root recognition visit successor) (code : Code root recognition visit successor bound) :
    word root recognition visit successor (prepend root recognition visit successor bound first code) =
      decode root recognition visit successor first :: word root recognition visit successor code := by
  simp only [word,prepend,List.ofFn_succ,List.map_cons,Fin.cases_zero,Fin.cases_succ]

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
