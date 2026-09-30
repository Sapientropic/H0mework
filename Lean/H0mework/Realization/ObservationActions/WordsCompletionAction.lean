import H0mework.Realization.ObservationActions.WordsCompletionEquivalence

/-! Every already allowed source letter acts on the old complete carrier through its existing autonomous Model. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords

open SourceGeneratedActionObservationHistory

noncomputable section
universe r u
variable {R : Type r} [CommRing R]
variable {I C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (actions : I → C →ₗ[R] C) (read : C →ₗ[R] B) (primary : I)

def completeAdvance (letter : I) :
    completion (actions primary) (inventory actions read) →ₗ[R] completion (actions primary) (inventory actions read) :=
  (completionEquiv actions read primary).conj (advance actions read primary letter)

theorem complete_advance_source (letter : I) (source : C) :
    completeAdvance actions read primary letter (sourceMap (actions primary) (inventory actions read) source) =
      sourceMap (actions primary) (inventory actions read) (actions letter source) := by
  change completionEquiv actions read primary
    (advance actions read primary letter ((completionEquiv actions read primary).symm
      (sourceMap (actions primary) (inventory actions read) source))) = _
  rw [completion_inverse_source, advance_source, completion_equiv_source]

theorem complete_primary_original : completeAdvance actions read primary primary =
    endomorphism (actions primary) (inventory actions read) := by
  apply LinearMap.ext
  intro value
  obtain ⟨source, rfl⟩ := full_source_surjective actions read primary value
  exact (complete_advance_source actions read primary primary source).trans
    (endomorphism_source (actions primary) (inventory actions read) source).symm

def completeRead (word : List I) : completion (actions primary) (inventory actions read) →ₗ[R] B :=
  (readout actions read primary word).comp (completionEquiv actions read primary).symm.toLinearMap

theorem complete_read_source (word : List I) (source : C) :
    completeRead actions read primary word (sourceMap (actions primary) (inventory actions read) source) =
      read (run actions word source) := by
  change readout actions read primary word
    ((completionEquiv actions read primary).symm (sourceMap (actions primary) (inventory actions read) source)) = _
  rw [completion_inverse_source, readout_source]

theorem complete_letter_readout (letter : I) (word : List I)
    (value : completion (actions primary) (inventory actions read)) :
    completeRead actions read primary word (completeAdvance actions read primary letter value) =
      completeRead actions read primary (letter :: word) value := by
  obtain ⟨source, rfl⟩ := full_source_surjective actions read primary value
  rw [complete_advance_source, complete_read_source, complete_read_source]
  rfl

theorem complete_run_source (word : List I) (source : C) :
    run (completeAdvance actions read primary) word (sourceMap (actions primary) (inventory actions read) source) =
      sourceMap (actions primary) (inventory actions read) (run actions word source) := by
  induction word generalizing source with
  | nil => rfl
  | cons letter rest previous =>
      change run (completeAdvance actions read primary) rest
        (completeAdvance actions read primary letter (sourceMap (actions primary) (inventory actions read) source)) = _
      rw [complete_advance_source, previous]
      rfl

theorem complete_run_model (word : List I) (value : completion (actions primary) (inventory actions read)) :
    (completionEquiv actions read primary).symm (run (completeAdvance actions read primary) word value) =
      run (advance actions read primary) word ((completionEquiv actions read primary).symm value) := by
  obtain ⟨source, rfl⟩ := full_source_surjective actions read primary value
  rw [complete_run_source, completion_inverse_source, completion_inverse_source, run_source]

end
end SourceGeneratedActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
