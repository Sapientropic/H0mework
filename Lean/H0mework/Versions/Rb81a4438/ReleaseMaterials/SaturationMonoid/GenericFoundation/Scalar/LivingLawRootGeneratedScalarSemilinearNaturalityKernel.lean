import Mathlib.Algebra.Star.Module
import H0mework.Realization.Perfectification.ScalarEnvelope

/-!
# Semilinear naturality of the scalar exact envelope

Source symmetries need not be linear over the identity coefficient map.
Complex conjugation is the motivating case.  This module transports an
actual semilinear source square through the same coimage and generated-dual
image.  No scalar forgetting is inserted.

The generic morphism records the ambient-dual action because that is the
source-owned datum which makes the square meaningful.  For an involutive
coefficient automorphism, `involutiveDualTarget` generates that action from
an actual semilinear map on the dual carrier.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarSemilinearNaturality

open SourceGeneratedScalarPerfectification
open SourceGeneratedScalarExactEnvelope

noncomputable section

universe r c d

variable {R : Type r} [CommRing R]
variable {C : Type c} {D : Type d}
variable [AddCommGroup C] [Module R C]
variable [AddCommGroup D] [Module R D]

variable {C' : Type c} {D' : Type d}
variable [AddCommGroup C'] [Module R C']
variable [AddCommGroup D'] [Module R D']

variable (evaluation : C →ₗ[R] Module.Dual R D)
variable (evaluation' : C' →ₗ[R] Module.Dual R D')
variable (σ : R →+* R)

/-- A source morphism whose coefficient action is retained in its type. -/
structure SourceMorphism where
  carrierMap : C →ₛₗ[σ] C'
  dualMap : Module.Dual R D →ₛₗ[σ] Module.Dual R D'
  naturality : dualMap.comp evaluation = evaluation'.comp carrierMap

namespace SourceMorphism

variable (morphism : SourceMorphism evaluation evaluation' σ)

theorem kernel_maps :
    LinearMap.ker evaluation ≤
      (LinearMap.ker evaluation').comap morphism.carrierMap := by
  intro value value_mem
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  have equality := LinearMap.congr_fun morphism.naturality value
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mem_ker.mp value_mem, map_zero] at equality
  exact equality.symm

/-- The semilinear map induced on the canonical coimages. -/
def inducedCarrierMap :
    SourceGeneratedScalarPerfectification.PerfectificationCarrier evaluation
        →ₛₗ[σ]
      SourceGeneratedScalarPerfectification.PerfectificationCarrier evaluation' :=
  (LinearMap.ker evaluation).mapQ (LinearMap.ker evaluation')
    morphism.carrierMap (morphism.kernel_maps evaluation evaluation')

@[simp] theorem carrierMap_comp_canonicalMap :
    (morphism.inducedCarrierMap evaluation evaluation' σ).comp
        (canonicalMap evaluation) =
      (canonicalMap evaluation').comp morphism.carrierMap := by
  exact Submodule.mapQ_mkQ _ _ _

theorem dualEmbedding_naturality :
    morphism.dualMap.comp (dualEmbedding evaluation) =
      (dualEmbedding evaluation').comp
        (morphism.inducedCarrierMap evaluation evaluation' σ) := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) quotientValue
  exact LinearMap.congr_fun morphism.naturality value

/-- The same source symmetry on the generated dual images. -/
def generatedDualMap :
    SourceGeneratedScalarExactEnvelope.GeneratedDual evaluation →ₛₗ[σ]
      SourceGeneratedScalarExactEnvelope.GeneratedDual evaluation' :=
  (morphism.dualMap.comp
      (SourceGeneratedScalarExactEnvelope.dualInclusion evaluation)).codRestrict
    (SourceGeneratedScalarExactEnvelope.GeneratedDual evaluation') (by
      intro value
      rcases value.property with ⟨carrierValue, equality⟩
      refine ⟨morphism.inducedCarrierMap evaluation evaluation' σ carrierValue, ?_⟩
      have commute := LinearMap.congr_fun
        (morphism.dualEmbedding_naturality evaluation evaluation') carrierValue
      exact commute.symm.trans (congrArg morphism.dualMap equality))

theorem generatedDualMap_naturality :
    (morphism.generatedDualMap evaluation evaluation').comp
        (SourceGeneratedScalarExactEnvelope.generatedDualMap evaluation) =
      (SourceGeneratedScalarExactEnvelope.generatedDualMap evaluation').comp
        (morphism.inducedCarrierMap evaluation evaluation' σ) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  exact LinearMap.congr_fun
    (morphism.dualEmbedding_naturality evaluation evaluation') value

theorem dualInclusion_naturality :
    (SourceGeneratedScalarExactEnvelope.dualInclusion evaluation').comp
        (morphism.generatedDualMap evaluation evaluation') =
      morphism.dualMap.comp
        (SourceGeneratedScalarExactEnvelope.dualInclusion evaluation) := by
  apply LinearMap.ext
  intro value
  rfl

theorem coevaluation_naturality :
    (morphism.inducedCarrierMap evaluation evaluation' σ).comp
        (SourceGeneratedScalarExactEnvelope.coevaluation evaluation) =
      (SourceGeneratedScalarExactEnvelope.coevaluation evaluation').comp
        (morphism.generatedDualMap evaluation evaluation') := by
  apply LinearMap.ext
  intro dualValue
  obtain ⟨carrierValue, rfl⟩ :=
    SourceGeneratedScalarExactEnvelope.generatedDualMap_surjective evaluation
      dualValue
  have sourceZigzag := LinearMap.congr_fun
    (SourceGeneratedScalarExactEnvelope.coevaluation_comp_generatedDualMap
      evaluation) carrierValue
  have targetZigzag := LinearMap.congr_fun
    (SourceGeneratedScalarExactEnvelope.coevaluation_comp_generatedDualMap
      evaluation')
    (morphism.inducedCarrierMap evaluation evaluation' σ carrierValue)
  have forwardNaturality := LinearMap.congr_fun
    (morphism.generatedDualMap_naturality evaluation evaluation') carrierValue
  rw [LinearMap.comp_apply] at sourceZigzag targetZigzag forwardNaturality
  simpa [sourceZigzag, forwardNaturality] using targetZigzag.symm

end SourceMorphism

/-! ## Generated ambient-dual action for involutive coefficients -/

variable [RingHomInvPair σ σ]

/-- Pull a dual functional through a `σ`-semilinear carrier map and apply
`σ` to its value.  Involutivity makes the result linear in the argument
and `σ`-semilinear in the functional. -/
def involutiveDualTarget (dualCarrierMap : D' →ₛₗ[σ] D) :
    Module.Dual R D →ₛₗ[σ] Module.Dual R D' where
  toFun functional :=
    { toFun := fun value => σ (functional (dualCarrierMap value))
      map_add' := by
        intro left right
        simp
      map_smul' := by
        intro scalar value
        rw [dualCarrierMap.map_smulₛₗ, map_smul]
        simp only [smul_eq_mul, map_mul, RingHomInvPair.comp_apply_eq,
          RingHom.id_apply] }
  map_add' := by
    intro left right
    apply LinearMap.ext
    intro value
    simp
  map_smul' := by
    intro scalar functional
    apply LinearMap.ext
    intro value
    simp

end
end SourceGeneratedScalarSemilinearNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
