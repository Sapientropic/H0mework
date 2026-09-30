import H0mework.Realization.ObservationActions.WordsCompletionAction

/-! The old original-restriction map carries completed word actions back to the unchanged observed completion. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords

open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual

noncomputable section
universe r u
variable {R : Type r} [CommRing R]
variable {I C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (actions : I → C →ₗ[R] C) (read : C →ₗ[R] B) (primary : I)

def completeRestriction : completion (actions primary) (inventory actions read) →ₗ[R] completion (actions primary) read :=
  ((LinearMap.range (sourceMap (actions primary) read)).subtype.comp
    (residualToRange (sourceMap (actions primary) read))).comp
      ((originalRestriction actions read primary).comp (completionEquiv actions read primary).symm.toLinearMap)

theorem complete_restriction_source (source : C) :
    completeRestriction actions read primary (sourceMap (actions primary) (inventory actions read) source) =
      sourceMap (actions primary) read source := by
  change (residualToRange (sourceMap (actions primary) read)
    (originalRestriction actions read primary ((completionEquiv actions read primary).symm
      (sourceMap (actions primary) (inventory actions read) source)))).val = _
  rw [completion_inverse_source, originalRestriction_source]
  rfl

theorem complete_restriction_primary (value : completion (actions primary) (inventory actions read)) :
    completeRestriction actions read primary (completeAdvance actions read primary primary value) =
      endomorphism (actions primary) read (completeRestriction actions read primary value) := by
  obtain ⟨source, rfl⟩ := full_source_surjective actions read primary value
  rw [complete_advance_source, complete_restriction_source, complete_restriction_source, endomorphism_source]

theorem complete_read_is_actual (word : List I) (value : completion (actions primary) (inventory actions read)) :
    completeRead actions read primary word value = stageRead (actions primary) (inventory actions read) 0 value 0 word := by
  obtain ⟨source, rfl⟩ := full_source_surjective actions read primary value
  rw [complete_read_source, source_reads_stage]
  rfl

end
end SourceGeneratedActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
