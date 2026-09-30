import H0mework.Probability.FullSource.Word

/-! A raw native function generates its complete-field linear map through the same whole source word. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullMap

open SourceGeneratedActionObservationHistory

noncomputable section

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable (stepX : X → X) (stepY : Y → Y) (native : X → Y)

def map : Field stepX (sourcePoint (State := X)) →ₗ[ℤ] Field stepY (sourcePoint (State := Y)) :=
  (sourceMap (sourceAction stepY) (observation sourcePoint)).comp
    ((Finsupp.lmapDomain ℤ ℤ native).comp (FullWord.word stepX))

theorem map_word (value : Field stepX (sourcePoint (State := X))) :
    FullWord.word stepY (map stepX stepY native value) =
      Finsupp.lmapDomain ℤ ℤ native (FullWord.word stepX value) :=
  FullWord.word_source stepY _

theorem map_source (word : Carrier X) :
    map stepX stepY native (sourceMap (sourceAction stepX) (observation sourcePoint) word) =
      sourceMap (sourceAction stepY) (observation sourcePoint) (Finsupp.lmapDomain ℤ ℤ native word) := by
  change sourceMap _ _ (Finsupp.lmapDomain ℤ ℤ native (FullWord.word stepX (sourceMap _ _ word))) = _
  rw [FullWord.word_source]

theorem map_point (state : X) :
    map stepX stepY native (fieldPoint stepX sourcePoint state) = fieldPoint stepY sourcePoint (native state) := by
  have source := map_source stepX stepY native (sourcePoint state)
  simpa only [fieldPoint, sourcePoint, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using source

theorem map_id : map stepX stepX id = LinearMap.id := by
  apply LinearMap.ext
  intro value
  apply FullWord.word_injective stepX
  simp only [map_word, Finsupp.lmapDomain_id, LinearMap.id_apply]

theorem map_comp (stepZ : Z → Z) (after : Y → Z) :
    (map stepY stepZ after).comp (map stepX stepY native) = map stepX stepZ (after ∘ native) := by
  apply LinearMap.ext
  intro value
  apply FullWord.word_injective stepZ
  change FullWord.word stepZ (map stepY stepZ after (map stepX stepY native value)) = _
  rw [map_word, map_word, map_word]
  exact (DFunLike.congr_fun (Finsupp.lmapDomain_comp ℤ ℤ native after) (FullWord.word stepX value)).symm

end
end SourceOwnedObservationHistory.FullMap
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
