import Mathlib.Algebra.Module.CharacterModule

/-!
# Generic character-double-dual exact perfectification

For every additive commutative group, evaluation against all characters into
the rational circle generates a canonical faithful map into the character
double dual.  Its exact image is the minimal source-generated character
ambient, functorial under integral-linear maps and universal for maps out of
the original carrier.

This construction accepts no finite, projective, torsion-free,
nondegeneracy, determinant, topology, or domain-specific premise.  It does
not claim that the whole double dual is source-surjective.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedCharacterDoubleDualExactPerfectification

universe u v w

variable (A : Type u) [AddCommGroup A]
variable (B : Type v) [AddCommGroup B]
variable (C : Type w) [AddCommGroup C]

abbrev DoubleDual (A : Type u) [AddCommGroup A] :=
  CharacterModule (CharacterModule A)

def evaluationAddHom : A →+ DoubleDual A where
  toFun := fun value =>
    { toFun := fun character => character value
      map_zero' := rfl
      map_add' := by intro left right; rfl }
  map_zero' := by
    apply CharacterModule.ext
    intro character
    exact character.map_zero
  map_add' := by
    intro left right
    apply CharacterModule.ext
    intro character
    exact character.map_add left right

def evaluation : A →ₗ[ℤ] DoubleDual A :=
  (evaluationAddHom A).toIntLinearMap

@[simp] theorem evaluation_apply
    (value : A) (character : CharacterModule A) :
    evaluation A value character = character value :=
  rfl

theorem evaluation_injective : Function.Injective (evaluation A) := by
  intro left right equality
  apply sub_eq_zero.mp
  apply CharacterModule.eq_zero_of_character_apply
  intro character
  rw [map_sub, sub_eq_zero]
  exact congrArg (fun evaluator : DoubleDual A => evaluator character) equality

abbrev ExactPerfectification := LinearMap.range (evaluation A)

def canonicalMap : A →ₗ[ℤ] ExactPerfectification A :=
  (evaluation A).codRestrict (LinearMap.range (evaluation A))
    (fun value => ⟨value, rfl⟩)

@[simp] theorem canonicalMap_val (value : A) :
    (canonicalMap A value : DoubleDual A) = evaluation A value :=
  rfl

theorem canonicalMap_injective : Function.Injective (canonicalMap A) := by
  intro left right equality
  apply evaluation_injective A
  exact congrArg Subtype.val equality

theorem canonicalMap_surjective : Function.Surjective (canonicalMap A) := by
  intro value
  rcases value.property with ⟨source, equality⟩
  refine ⟨source, Subtype.ext ?_⟩
  exact equality

noncomputable def canonicalEquiv : A ≃ₗ[ℤ] ExactPerfectification A :=
  LinearEquiv.ofInjective (evaluation A) (evaluation_injective A)

@[simp] theorem canonicalEquiv_apply (value : A) :
    canonicalEquiv A value = canonicalMap A value :=
  rfl

def characterPullback (map : A →ₗ[ℤ] B) :
    CharacterModule B →ₗ[ℤ] CharacterModule A :=
  { toFun := fun character => character.comp map.toAddMonoidHom
    map_add' := by intro left right; rfl
    map_smul' := by intro scalar character; ext value; rfl }

def doubleDualMap (map : A →ₗ[ℤ] B) : DoubleDual A →ₗ[ℤ] DoubleDual B :=
  characterPullback (CharacterModule B) (CharacterModule A)
    (characterPullback A B map)

@[simp] theorem doubleDualMap_evaluation
    (map : A →ₗ[ℤ] B) (value : A) :
    doubleDualMap A B map (evaluation A value) = evaluation B (map value) := by
  apply CharacterModule.ext
  intro character
  rfl

def perfectificationMap (map : A →ₗ[ℤ] B) :
    ExactPerfectification A →ₗ[ℤ] ExactPerfectification B :=
  LinearMap.codRestrict (LinearMap.range (evaluation B))
    ((doubleDualMap A B map).comp
      (LinearMap.range (evaluation A)).subtype) (by
        intro value
        rcases value.property with ⟨source, equality⟩
        refine ⟨map source, ?_⟩
        change evaluation B (map source) =
          doubleDualMap A B map (value : DoubleDual A)
        rw [← equality, doubleDualMap_evaluation])

@[simp] theorem perfectificationMap_canonicalMap
    (map : A →ₗ[ℤ] B) (value : A) :
    perfectificationMap A B map (canonicalMap A value) =
      canonicalMap B (map value) := by
  apply Subtype.ext
  exact doubleDualMap_evaluation A B map value

theorem canonical_naturality (map : A →ₗ[ℤ] B) :
    (perfectificationMap A B map).comp (canonicalMap A) =
      (canonicalMap B).comp map := by
  apply LinearMap.ext
  intro value
  exact perfectificationMap_canonicalMap A B map value

@[simp] theorem perfectificationMap_id :
    perfectificationMap A A LinearMap.id = LinearMap.id := by
  apply LinearMap.ext
  intro value
  obtain ⟨source, rfl⟩ := canonicalMap_surjective A value
  simp

theorem perfectificationMap_comp
    (first : A →ₗ[ℤ] B) (second : B →ₗ[ℤ] C) :
    perfectificationMap A C (second.comp first) =
      (perfectificationMap B C second).comp
        (perfectificationMap A B first) := by
  apply LinearMap.ext
  intro value
  obtain ⟨source, rfl⟩ := canonicalMap_surjective A value
  simp

theorem range_minimal
    (submodule : Submodule ℤ (DoubleDual A))
    (contains : ∀ value : A, evaluation A value ∈ submodule) :
    LinearMap.range (evaluation A) ≤ submodule := by
  rintro value ⟨source, rfl⟩
  exact contains source

noncomputable def universalFactor (map : A →ₗ[ℤ] B) :
    ExactPerfectification A →ₗ[ℤ] B :=
  map.comp (canonicalEquiv A).symm.toLinearMap

@[simp] theorem universalFactor_canonicalMap
    (map : A →ₗ[ℤ] B) :
    (universalFactor A B map).comp (canonicalMap A) = map := by
  apply LinearMap.ext
  intro value
  change map ((canonicalEquiv A).symm (canonicalMap A value)) = map value
  rw [← canonicalEquiv_apply, LinearEquiv.symm_apply_apply]

theorem universalFactor_unique
    (map : A →ₗ[ℤ] B)
    (candidate : ExactPerfectification A →ₗ[ℤ] B)
    (commutes : candidate.comp (canonicalMap A) = map) :
    candidate = universalFactor A B map := by
  apply LinearMap.ext
  intro value
  obtain ⟨source, rfl⟩ := canonicalMap_surjective A value
  have candidateRead := LinearMap.congr_fun commutes source
  rw [LinearMap.comp_apply] at candidateRead
  rw [candidateRead]
  change map source = map ((canonicalEquiv A).symm (canonicalMap A source))
  rw [← canonicalEquiv_apply, LinearEquiv.symm_apply_apply]


end SourceGeneratedCharacterDoubleDualExactPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
