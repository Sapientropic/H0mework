import H0mework.Probability.FullSource.Map

/-! The actual two source actions generate a dynamic defect and its composition law. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullMap

noncomputable section

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable (stepX : X → X) (stepY : Y → Y) (native : X → Y)

def defect : Field stepX (sourcePoint (State := X)) →ₗ[ℤ] Field stepY (sourcePoint (State := Y)) :=
  (fieldAction stepY sourcePoint).comp (map stepX stepY native) -
    (map stepX stepY native).comp (fieldAction stepX sourcePoint)

theorem defect_point (state : X) :
    defect stepX stepY native (fieldPoint stepX sourcePoint state) =
      fieldPoint stepY sourcePoint (stepY (native state)) -
        fieldPoint stepY sourcePoint (native (stepX state)) := by
  simp only [defect, LinearMap.sub_apply, LinearMap.comp_apply, map_point, fieldPoint_action]

theorem defect_word (value : Field stepX (sourcePoint (State := X))) :
    FullWord.word stepY (defect stepX stepY native value) =
      sourceAction stepY (Finsupp.lmapDomain ℤ ℤ native (FullWord.word stepX value)) -
        Finsupp.lmapDomain ℤ ℤ native (sourceAction stepX (FullWord.word stepX value)) := by
  simp only [defect, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, FullWord.word_action, map_word]

theorem defect_comp (stepZ : Z → Z) (after : Y → Z) :
    defect stepX stepZ (after ∘ native) =
      (defect stepY stepZ after).comp (map stepX stepY native) +
        (map stepY stepZ after).comp (defect stepX stepY native) := by
  rw [defect, ← map_comp stepX stepY native stepZ after]
  apply LinearMap.ext
  intro value
  simp only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub]
  abel

/-- Vanishing reads back the native local action law; it is never a map-constructor input. -/
theorem defect_zero_iff : defect stepX stepY native = 0 ↔
    ∀ state, stepY (native state) = native (stepX state) := by
  constructor
  · intro vanished state
    have point := DFunLike.congr_fun vanished (fieldPoint stepX sourcePoint state)
    change defect stepX stepY native (fieldPoint stepX sourcePoint state) = 0 at point
    rw [defect_point] at point
    exact full_fieldPoint_injective stepY (sub_eq_zero.mp point)
  · intro sourceLaw
    have square : stepY ∘ native = native ∘ stepX := funext sourceLaw
    apply LinearMap.ext
    intro value
    apply FullWord.word_injective stepY
    change FullWord.word stepY (defect stepX stepY native value) = FullWord.word stepY 0
    rw [defect_word, map_zero]
    change Finsupp.mapDomain stepY (Finsupp.mapDomain native (FullWord.word stepX value)) -
      Finsupp.mapDomain native (Finsupp.mapDomain stepX (FullWord.word stepX value)) = 0
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, square, sub_self]

end
end SourceOwnedObservationHistory.FullMap
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
