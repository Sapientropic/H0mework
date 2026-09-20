import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Faithful integral action disposition

A source-owned integral face is an additive carrier with a faithful map into
an ambient carrier.  An ambient action either restricts uniquely to that face
or sends an actual face coordinate outside its realized range.  The latter is
the exact representation residual; no finite, projective, determinant,
nondegeneracy, or inverse premise enters the construction.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFaithfulIntegralFace

noncomputable section

universe l a

variable {L : Type l} [AddCommGroup L]
variable {Ambient : Type a} [AddCommGroup Ambient]

/-- A genuine integral dependent face.  Its carrier deliberately has only
the canonical `ℤ`-module structure; closing it under all ambient scalars would
erase the non-localized information that this interface is meant to retain. -/
structure FaithfulIntegralFace where
  realization : L →ₗ[ℤ] Ambient
  injective : Function.Injective realization

/-- The ambient action preserves every actual integral coordinate. -/
def PreservesFace
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient) : Prop :=
  ∀ value : L,
    action (face.realization value) ∈ LinearMap.range face.realization

/-- The unique integral restriction of one ambient action. -/
structure ActionLift
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient) where
  integralAction : L →ₗ[ℤ] L
  commutes : face.realization.comp integralAction =
    action.comp face.realization

/-- Faithfulness turns pointwise preservation into an actual linear action;
linearity is generated rather than supplied by a caller. -/
noncomputable def inducedIntegralAction
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient)
    (preserves : PreservesFace face action) : L →ₗ[ℤ] L where
  toFun value := Classical.choose (preserves value)
  map_add' left right := by
    apply face.injective
    have leftSpec := Classical.choose_spec (preserves left)
    have rightSpec := Classical.choose_spec (preserves right)
    have sumSpec := Classical.choose_spec (preserves (left + right))
    simpa only [map_add, leftSpec, rightSpec] using sumSpec
  map_smul' scalar value := by
    apply face.injective
    have valueSpec := Classical.choose_spec (preserves value)
    have smulSpec := Classical.choose_spec (preserves (scalar • value))
    simpa only [map_smul, RingHom.id_apply, valueSpec] using smulSpec

def actionLiftOfPreserves
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient)
    (preserves : PreservesFace face action) : ActionLift face action where
  integralAction := inducedIntegralAction face action preserves
  commutes := by
    apply LinearMap.ext
    intro value
    exact Classical.choose_spec (preserves value)

theorem actionLift_unique
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient)
    (first second : ActionLift face action) :
    first.integralAction = second.integralAction := by
  apply LinearMap.ext
  intro value
  apply face.injective
  have firstAt := LinearMap.congr_fun first.commutes value
  have secondAt := LinearMap.congr_fun second.commutes value
  exact firstAt.trans secondAt.symm

theorem actionLift_nonempty_iff_preserves
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient) :
    Nonempty (ActionLift face action) ↔ PreservesFace face action := by
  constructor
  · rintro ⟨lift⟩ value
    refine ⟨lift.integralAction value, ?_⟩
    exact LinearMap.congr_fun lift.commutes value
  · intro preserves
    exact ⟨actionLiftOfPreserves face action preserves⟩

/-- An actual source coordinate whose ambient image leaves the current
integral observation language. -/
structure ActionEscapeCoordinate
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient) where
  source : L
  escapes : action (face.realization source) ∉
    LinearMap.range face.realization

inductive ActionDisposition
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient) : Type (max l a) where
  | stable (lift : ActionLift face action)
  | representationResidual (coordinate : ActionEscapeCoordinate face action)

/-- Every faithful integral face has a complete action disposition. -/
noncomputable def settleAction
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient) :
    ActionDisposition face action := by
  classical
  by_cases preserves : PreservesFace face action
  · exact .stable (actionLiftOfPreserves face action preserves)
  · have escape : ∃ value : L,
        action (face.realization value) ∉
          LinearMap.range face.realization := by
      simpa [PreservesFace] using preserves
    exact .representationResidual ⟨escape.choose, escape.choose_spec⟩

theorem actionDisposition_total
    (face : FaithfulIntegralFace (L := L) (Ambient := Ambient))
    (action : Ambient →ₗ[ℤ] Ambient) :
    Nonempty (ActionDisposition face action) :=
  ⟨settleAction face action⟩

end
end SourceGeneratedFaithfulIntegralFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
