import H0mework.Probability.FullSource.Word
import H0mework.Realization.Operations.BinaryInputs

/-! Complete source fields consume the original native binary and correlated-joint producers. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullBinary

open SourceGeneratedActionObservationHistory

noncomputable section

universe u

variable {X Y Z : Type u}
variable (stepX : X → X) (stepY : Y → Y) (stepZ : Z → Z) (native : X → Y → Z)

def binary : Field stepX (sourcePoint (State := X)) →+
    Field stepY (sourcePoint (State := Y)) →+ Field stepZ (sourcePoint (State := Z)) :=
  let output : Carrier Z →+ Field stepZ (sourcePoint (State := Z)) :=
    (sourceMap (sourceAction stepZ) (observation sourcePoint)).toAddMonoidHom
  let inputLeft := (FullWord.word stepX).toAddMonoidHom
  let inputRight := (FullWord.word stepY).toAddMonoidHom
  { toFun := fun left => output.comp ((SourceNativeBinary.lift native (inputLeft left)).comp inputRight)
    map_zero' := by
      ext right
      simp only [AddMonoidHom.comp_apply, map_zero, AddMonoidHom.zero_apply]
    map_add' := by
      intro left right
      ext value
      simp only [AddMonoidHom.comp_apply, map_add, AddMonoidHom.add_apply] }

theorem binary_word (left : Field stepX (sourcePoint (State := X)))
    (right : Field stepY (sourcePoint (State := Y))) :
    FullWord.word stepZ (binary stepX stepY stepZ native left right) =
      SourceNativeBinary.linear native (FullWord.word stepX left) (FullWord.word stepY right) :=
  FullWord.word_source stepZ _

theorem binary_source (left : Carrier X) (right : Carrier Y) :
    binary stepX stepY stepZ native
        (sourceMap (sourceAction stepX) (observation sourcePoint) left)
        (sourceMap (sourceAction stepY) (observation sourcePoint) right) =
      sourceMap (sourceAction stepZ) (observation sourcePoint) (SourceNativeBinary.linear native left right) := by
  change sourceMap _ _ (SourceNativeBinary.linear native (FullWord.word stepX (sourceMap _ _ left))
    (FullWord.word stepY (sourceMap _ _ right))) = _
  rw [FullWord.word_source, FullWord.word_source]

theorem binary_point (left : X) (right : Y) :
    binary stepX stepY stepZ native (fieldPoint stepX sourcePoint left) (fieldPoint stepY sourcePoint right) =
      fieldPoint stepZ sourcePoint (native left right) :=
  (binary_source stepX stepY stepZ native (sourcePoint left) (sourcePoint right)).trans
    (congrArg (sourceMap (sourceAction stepZ) (observation sourcePoint))
      (SourceNativeBinary.lift_point native left right))

theorem binary_mixed_update (left incrementLeft : Field stepX (sourcePoint (State := X)))
    (right incrementRight : Field stepY (sourcePoint (State := Y))) :
    binary stepX stepY stepZ native (left + incrementLeft) (right + incrementRight) =
      binary stepX stepY stepZ native left right +
        (binary stepX stepY stepZ native left incrementRight +
          binary stepX stepY stepZ native incrementLeft right +
          binary stepX stepY stepZ native incrementLeft incrementRight) := by
  simp only [map_add, AddMonoidHom.add_apply]
  abel

/-- Existing joint words enter intact, before any separate marginal observation. -/
def pushJoint : Field (Prod.map stepX stepY) (sourcePoint (State := X × Y)) →ₗ[ℤ]
    Field stepZ (sourcePoint (State := Z)) :=
  (sourceMap (sourceAction stepZ) (observation sourcePoint)).comp
    ((SourceNativeBinary.pushJoint native).comp (FullWord.word (Prod.map stepX stepY)))

theorem pushJoint_source (joint : Carrier (X × Y)) :
    pushJoint stepX stepY stepZ native
        (sourceMap (sourceAction (Prod.map stepX stepY)) (observation sourcePoint) joint) =
      sourceMap (sourceAction stepZ) (observation sourcePoint) (SourceNativeBinary.pushJoint native joint) := by
  change sourceMap _ _ (SourceNativeBinary.pushJoint native
    (FullWord.word (Prod.map stepX stepY) (sourceMap _ _ joint))) = _
  rw [FullWord.word_source]

theorem pushJoint_word (joint : Field (Prod.map stepX stepY) (sourcePoint (State := X × Y))) :
    FullWord.word stepZ (pushJoint stepX stepY stepZ native joint) =
      SourceNativeBinary.pushJoint native (FullWord.word (Prod.map stepX stepY) joint) :=
  FullWord.word_source stepZ _

theorem pushJoint_point (left : X) (right : Y) :
    pushJoint stepX stepY stepZ native (fieldPoint (Prod.map stepX stepY) sourcePoint (left, right)) =
      fieldPoint stepZ sourcePoint (native left right) :=
  (pushJoint_source stepX stepY stepZ native (sourcePoint (left, right))).trans
    (congrArg (sourceMap (sourceAction stepZ) (observation sourcePoint))
      (SourceNativeBinary.pushJoint_point native left right))

theorem binary_through_joint (left : Field stepX (sourcePoint (State := X)))
    (right : Field stepY (sourcePoint (State := Y))) :
    binary stepX stepY stepZ native left right =
      pushJoint stepX stepY stepZ native
        (sourceMap (sourceAction (Prod.map stepX stepY)) (observation sourcePoint)
          (SourceNativeBinary.joint (FullWord.word stepX left) (FullWord.word stepY right))) := by
  rw [pushJoint_source]
  rfl

end
end SourceOwnedObservationHistory.FullBinary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
