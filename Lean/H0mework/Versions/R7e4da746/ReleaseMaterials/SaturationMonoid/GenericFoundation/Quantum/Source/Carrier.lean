import H0mework.Realization.Feature.HilbertRealization
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The completed action orbit of a source vector is its original Hilbert
carrier. All bounded source actions are retained, including actions leaving
the occupied subspace. No invariant-vector condition is used. -/

set_option autoImplicit false
open scoped InnerProductSpace

namespace SaturationMonoid.Quantum.Source
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedComplexFeaturePerfectification
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Ω : H) (unit : ‖Ω‖ = 1)

def feature : (H →L[ℂ] H) →ₗ[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H Ω).toLinearMap

abbrev Carrier := HilbertAmbient (feature Ω)

def vector : (H →L[ℂ] H) →ₗ[ℂ] Carrier Ω := canonicalHilbertMap (feature Ω)

include unit

omit [CompleteSpace H] in
theorem feature_surjective : Function.Surjective (feature Ω) := by
  intro v
  refine ⟨(innerSL ℂ Ω).smulRight v, ?_⟩
  change (inner ℂ Ω Ω) • v = v
  rw [inner_self_eq_norm_sq_to_K, unit]
  simp

theorem realization_surjective : Function.Surjective (hilbertAmbientRealization (feature Ω)) := by
  intro v
  obtain ⟨A, rfl⟩ := feature_surjective Ω unit v
  exact ⟨vector Ω A, hilbertAmbientRealization_source_readback (feature Ω) A⟩

def realization : Carrier Ω ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (hilbertAmbientRealization (feature Ω))
    (realization_surjective Ω unit)

theorem realization_vector (A : H →L[ℂ] H) :
    realization Ω unit (vector Ω A) = A Ω :=
  hilbertAmbientRealization_source_readback (feature Ω) A

theorem vector_surjective : Function.Surjective (vector Ω) := by
  intro x
  obtain ⟨A, hA⟩ := feature_surjective Ω unit (realization Ω unit x)
  refine ⟨A, (realization Ω unit).injective ?_⟩
  exact (realization_vector Ω unit A).trans hA

def action (A : H →L[ℂ] H) : Carrier Ω →L[ℂ] Carrier Ω :=
  (realization Ω unit).symm.conjStarAlgEquiv A

theorem action_star (A : H →L[ℂ] H) :
    action Ω unit (star A) = star (action Ω unit A) :=
  map_star (realization Ω unit).symm.conjStarAlgEquiv A

theorem realization_action (A : H →L[ℂ] H) (x : Carrier Ω) :
    realization Ω unit (action Ω unit A x) = A (realization Ω unit x) :=
  (realization Ω unit).apply_symm_apply _

theorem action_vector (A B : H →L[ℂ] H) :
    action Ω unit A (vector Ω B) = vector Ω (A * B) := by
  apply (realization Ω unit).injective
  rw [realization_action, realization_vector, realization_vector]
  rfl

theorem action_faithful : Function.Injective (action Ω unit) := by
  intro A B same
  ext v
  obtain ⟨x, rfl⟩ := (realization Ω unit).surjective v
  exact (realization_action Ω unit A x).symm.trans
    ((congrArg (fun T => realization Ω unit (T x)) same).trans
      (realization_action Ω unit B x))

theorem gram (A B : H →L[ℂ] H) :
    inner ℂ (vector Ω A) (vector Ω B) = inner ℂ (A Ω) (B Ω) := by
  rw [← (realization Ω unit).inner_map_map, realization_vector, realization_vector]

theorem gram_adjoint (A B : H →L[ℂ] H) :
    inner ℂ (vector Ω A) (vector Ω B) = inner ℂ Ω ((A.adjoint * B) Ω) := by
  rw [gram Ω unit]
  exact (ContinuousLinearMap.adjoint_inner_right A Ω (B Ω)).symm

theorem action_word (word : List (H →L[ℂ] H)) :
    (word.map (action Ω unit)).prod (vector Ω 1) = vector Ω word.prod := by
  induction word with
  | nil => rfl
  | cons A word ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
      rw [ih, action_vector]

omit unit [CompleteSpace H] in
theorem source_kernel : LinearMap.ker (vector Ω) = LinearMap.ker (feature Ω) :=
  canonicalHilbertMap_ker (feature Ω)

end
end SaturationMonoid.Quantum.Source
