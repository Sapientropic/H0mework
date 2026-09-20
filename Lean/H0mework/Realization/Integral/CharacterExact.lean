import H0mework.Realization.Integral.CharacterDoubleDual

/-! The existing faithful character evaluation and its actual maps retain arbitrary scalar actions. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCharacterExact

noncomputable section

universe r u v w

abbrev DoubleDual (A : Type u) [AddCommGroup A] :=
  SourceGeneratedCharacterDoubleDualExactPerfectification.DoubleDual A

variable (R : Type r) [CommRing R]
variable (A : Type u) [AddCommGroup A] [Module R A]

/-- The original additive evaluation is scalar-linear under the existing double character action. -/
def evaluation : A →ₗ[R] DoubleDual A where
  toFun := SourceGeneratedCharacterDoubleDualExactPerfectification.evaluationAddHom A
  map_add' := (SourceGeneratedCharacterDoubleDualExactPerfectification.evaluationAddHom A).map_add
  map_smul' := by
    intro scalar value
    apply CharacterModule.ext
    intro character
    rfl

@[simp] theorem evaluation_apply (value : A) (character : CharacterModule A) :
    evaluation R A value character = character value := rfl

theorem evaluation_injective : Function.Injective (evaluation R A) :=
  SourceGeneratedCharacterDoubleDualExactPerfectification.evaluation_injective A

abbrev Carrier := LinearMap.range (evaluation R A)

def canonicalMap : A →ₗ[R] Carrier R A :=
  (evaluation R A).rangeRestrict

@[simp] theorem canonicalMap_val (value : A) :
    (canonicalMap R A value : DoubleDual A) = evaluation R A value := rfl

theorem canonicalMap_injective : Function.Injective (canonicalMap R A) := by
  intro left right same
  exact evaluation_injective R A (congrArg Subtype.val same)

theorem canonicalMap_surjective : Function.Surjective (canonicalMap R A) :=
  (evaluation R A).surjective_rangeRestrict

def equiv : A ≃ₗ[R] Carrier R A :=
  LinearEquiv.ofInjective (evaluation R A) (evaluation_injective R A)

@[simp] theorem equiv_apply (value : A) : equiv R A value = canonicalMap R A value := rfl

variable {R A}
variable {B : Type v} [AddCommGroup B] [Module R B]
variable {C : Type w} [AddCommGroup C] [Module R C]

/-- The source map acts by the two existing contravariant character maps. -/
def doubleDualMap (sourceMap : A →ₗ[R] B) : DoubleDual A →ₗ[R] DoubleDual B :=
  CharacterModule.dual (CharacterModule.dual sourceMap)

@[simp] theorem doubleDualMap_evaluation (sourceMap : A →ₗ[R] B) (value : A) :
    doubleDualMap sourceMap (evaluation R A value) = evaluation R B (sourceMap value) := by
  apply CharacterModule.ext
  intro character
  rfl

def map (sourceMap : A →ₗ[R] B) : Carrier R A →ₗ[R] Carrier R B :=
  ((doubleDualMap sourceMap).comp (LinearMap.range (evaluation R A)).subtype).codRestrict
    (LinearMap.range (evaluation R B)) (by
      rintro value
      obtain ⟨source, source_eq⟩ := value.property
      refine ⟨sourceMap source, ?_⟩
      change evaluation R B (sourceMap source) = doubleDualMap sourceMap value.val
      rw [← source_eq, doubleDualMap_evaluation])

@[simp] theorem map_canonicalMap (sourceMap : A →ₗ[R] B) (value : A) :
    map sourceMap (canonicalMap R A value) = canonicalMap R B (sourceMap value) := by
  apply Subtype.ext
  exact doubleDualMap_evaluation sourceMap value

theorem canonical_naturality (sourceMap : A →ₗ[R] B) :
    (map sourceMap).comp (canonicalMap R A) = (canonicalMap R B).comp sourceMap := by
  apply LinearMap.ext
  intro value
  exact map_canonicalMap sourceMap value

@[simp] theorem map_id : map (LinearMap.id : A →ₗ[R] A) = LinearMap.id := by
  ext value
  obtain ⟨source, rfl⟩ := canonicalMap_surjective R A value
  simp

theorem map_comp (first : A →ₗ[R] B) (second : B →ₗ[R] C) :
    map (second.comp first) = (map second).comp (map first) := by
  ext value
  obtain ⟨source, rfl⟩ := canonicalMap_surjective R A value
  simp

/-- An independent source readout factors through the faithful exact image. -/
def factor (readout : A →ₗ[R] B) : Carrier R A →ₗ[R] B :=
  readout.comp (equiv R A).symm.toLinearMap

@[simp] theorem factor_canonicalMap (readout : A →ₗ[R] B) :
    (factor readout).comp (canonicalMap R A) = readout := by
  ext value
  change readout ((equiv R A).symm (canonicalMap R A value)) = readout value
  rw [← equiv_apply, LinearEquiv.symm_apply_apply]

theorem factor_unique (readout : A →ₗ[R] B) (candidate : Carrier R A →ₗ[R] B)
    (commutes : candidate.comp (canonicalMap R A) = readout) : candidate = factor readout := by
  ext value
  obtain ⟨source, rfl⟩ := canonicalMap_surjective R A value
  have sourceRead := LinearMap.congr_fun commutes source
  have factorRead := LinearMap.congr_fun (factor_canonicalMap readout) source
  exact sourceRead.trans factorRead.symm

end
end SourceGeneratedScalarCharacterExact
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
