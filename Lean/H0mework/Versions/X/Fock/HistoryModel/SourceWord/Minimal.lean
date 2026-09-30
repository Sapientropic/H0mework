import H0mework.Versions.X.Fock.HistoryModel.SourceWord.Information
import H0mework.Versions.X.Fock.HistoryConditional.ActualImageMinimal
import H0mework.Versions.X.Fock.HistoryConditional.GWordInverseSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordMinimalCode

open SourceGeneratedActionWords SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation SourceConditionalModel
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

def wordRead (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) : Fock.WholeModel (inventoryBound runtime + 1) :=
  run (Fock.letterAction (inventoryBound runtime + 1)) word
    (Fock.point (inventoryBound runtime + 1)
      (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current))

def executed (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) : Current :=
  Fock.actualWord (inventoryBound runtime + 1) word
    (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current)

theorem wordRead_point (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    wordRead runtime word actor = Fock.point (inventoryBound runtime + 1) (executed runtime word actor) :=
  Fock.word_point (inventoryBound runtime + 1) word _

/-- Equality in the existing canonical word quotient is exactly equality of all original consumers. -/
theorem canonical_consumer_fibre (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (left right : Actors runtime) :
    wordRead runtime word left = wordRead runtime word right ↔
      ∀ tail : List (Fock.Letter (inventoryBound runtime + 1)),
        Fock.observer (inventoryBound runtime + 1)
          (run (Fock.actions (inventoryBound runtime + 1)) tail
            (sourcePoint (executed runtime word left))) =
        Fock.observer (inventoryBound runtime + 1)
          (run (Fock.actions (inventoryBound runtime + 1)) tail
            (sourcePoint (executed runtime word right))) := by
  rw [wordRead_point, wordRead_point]
  exact SourceGeneratedActionWords.projection_fibre
    (Fock.actions (inventoryBound runtime + 1)) (Fock.observer (inventoryBound runtime + 1))
    (.inl ()) (sourcePoint (executed runtime word left)) (sourcePoint (executed runtime word right))

abbrev WordImage (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :=
  Set.range (wordRead runtime word)

theorem wordRead_injective (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    Function.Injective (wordRead runtime word) :=
  SourceWordDynamicNext.actor_word_injective runtime word

theorem canonical_consumer_actor_fibre (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (left right : Actors runtime) :
    (∀ tail : List (Fock.Letter (inventoryBound runtime + 1)),
        Fock.observer (inventoryBound runtime + 1)
          (run (Fock.actions (inventoryBound runtime + 1)) tail
            (sourcePoint (executed runtime word left))) =
        Fock.observer (inventoryBound runtime + 1)
          (run (Fock.actions (inventoryBound runtime + 1)) tail
            (sourcePoint (executed runtime word right)))) ↔ left = right := by
  rw [← canonical_consumer_fibre]
  exact ⟨fun same => wordRead_injective runtime word same,
    fun same => congrArg (wordRead runtime word) same⟩

def wordEquiv (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    Actors runtime ≃ WordImage runtime word :=
  Equiv.ofInjective (wordRead runtime word) (wordRead_injective runtime word)

noncomputable instance (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    Fintype (WordImage runtime word) :=
  Fintype.ofEquiv (Actors runtime) (wordEquiv runtime word)

/-- The actual reachable word image itself is an exact finite code. -/
theorem word_image_card (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    Fintype.card (WordImage runtime word) = inventoryBound runtime + 1 := by
  have same := Fintype.card_congr (wordEquiv runtime word)
  simpa only [Fintype.card_fin] using same.symm

def decode (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    WordImage runtime word → SourceJointClockGraph.Carrier :=
  fun code => SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word
    ((wordEquiv runtime word).symm code)

/-- No target witness enters the code constructor: the old physical task is read from its actor. -/
theorem decode_actual (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    decode runtime word (wordEquiv runtime word actor) =
      SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor := by
  simp only [decode, Equiv.symm_apply_apply]

/-- The code's G decoder agrees with the existing native-history physical decoder. -/
theorem decode_native_history (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    decode runtime word (wordEquiv runtime word actor) =
      SourceCompiledGWord.effect (inventoryBound runtime + 1) word
        (SourceConditionalNativePosterior.decoder runtime
          (SourceCopyNativeHistory.read (inventoryBound runtime))
          (SourceCopyNativeHistory.read (inventoryBound runtime) actor.val)) := by
  rw [decode_actual]
  exact (SourceCompiledGWord.history_recovers runtime (inventoryBound runtime + 1) word actor).symm

/-- Every code fibre has exactly its original actor, including all possible inverse fibres. -/
theorem actor_fibre (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (code : WordImage runtime word) (actor : Actors runtime) :
    wordEquiv runtime word actor = code ↔ actor = (wordEquiv runtime word).symm code := by
  exact (wordEquiv runtime word).eq_symm_apply.symm

/-- The source-law mass at each reachable code is the unmodified original actor weight. -/
theorem code_mass (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (code : WordImage runtime word) :
    ((((Fock.sourceLaw (inventoryBound runtime)).map nativeStep).map
      (Fock.actualWord (inventoryBound runtime + 1) word)).map
        (Fock.point (inventoryBound runtime + 1))) code.val =
      historyPMF (inventoryBound runtime) ((wordEquiv runtime word).symm code) := by
  obtain ⟨actor, rfl⟩ := (wordEquiv runtime word).surjective code
  rw [Equiv.symm_apply_apply]
  have actual : ((wordEquiv runtime word actor).val) = wordRead runtime word actor := by
    rw [wordEquiv, Equiv.ofInjective_apply]
  rw [actual]
  exact SourceWordDynamicNext.source_word_mass runtime word actor

/-- Recovery of the same acted physical G task forces the old faithful-code lower bound. -/
theorem any_faithful_code_lower (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    {Code : Type*} [Fintype Code]
    (encode : WordImage runtime word → Code)
    (candidateDecoder : Code → SourceJointClockGraph.Carrier)
    (recovers : ∀ actor : Actors runtime,
      candidateDecoder (encode (wordEquiv runtime word actor)) =
        SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor) :
    inventoryBound runtime + 1 ≤ Fintype.card Code := by
  apply SourceActualImageStep.faithful_code_lower runtime
    (fun actor => encode (wordEquiv runtime word actor))
    (fun code => SourceGWordInverse.recover (inventoryBound runtime + 1) word (candidateDecoder code))
  intro actor
  rw [recovers actor, SourceCompiledGWord.image_original]
  exact SourceGWordInverse.recover_effect (inventoryBound runtime + 1) word
    (SourceConditionalInventory.values (inventoryBound runtime) actor)

/-- The real index-1 copy word at runtime 3 has four source actors, so one code state cannot recover G. -/
theorem actual_copy_word_no_unit_code
    (encode : WordImage (runtimeAt 3) [SourceWordDynamicNext.copyOne] → Unit)
    (candidateDecoder : Unit → SourceJointClockGraph.Carrier) :
    ¬ ∀ actor : Actors (runtimeAt 3),
      candidateDecoder (encode (wordEquiv (runtimeAt 3) [SourceWordDynamicNext.copyOne] actor)) =
        SourceCompiledGWord.image (runtimeAt 3)
          (inventoryBound (runtimeAt 3) + 1) [SourceWordDynamicNext.copyOne] actor := by
  intro recovers
  have lower := any_faithful_code_lower (runtimeAt 3) [SourceWordDynamicNext.copyOne]
    encode candidateDecoder recovers
  rw [inventory_bound, runtimeAt_state] at lower
  norm_num at lower

end
end SourceWordMinimalCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
