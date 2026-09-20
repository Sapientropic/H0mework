import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import H0mework.Realization.Perfectification.SourceCoimage

/-!
# Source-generated perfect ambient extension

The coimage `P := C / ker(e)` is the canonical lossless carrier for the
generated dual evaluation.  When the source has also generated finite-free
evidence for `P`, the hyperbolic carrier `Dual(P) × P` is a canonical perfect
ambient: its pairing is the actual `dualProd` pairing, and the source enters
through the second summand.  The construction is not allowed to assume that
evidence.  The total disposition therefore returns either this ambient or an
exact finite/nonfree or representation residual.

This is the next generic layer above the coimage mouth.  It deliberately does
not claim that every module admits a finite perfect ambient; the infinite-rank
branch is a representation/compression residual and an explicit signal that a
larger carrier category is required.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedPerfectAmbient

open SourceGeneratedPerfectification

noncomputable section

universe c d

variable {C : Type c} {D : Type d}
variable [AddCommGroup C] [AddCommGroup D]
variable (evaluation : C →ₗ[ℤ] Module.Dual ℤ D)

abbrev Perfectification := PerfectificationCarrier evaluation

/-- The canonical hyperbolic carrier built from the source-generated
coimage. -/
abbrev HyperbolicCarrier :=
  Module.Dual ℤ (Perfectification evaluation) × Perfectification evaluation

/-- Actual hyperbolic pairing on the ambient carrier. -/
def hyperbolicPairing : HyperbolicCarrier evaluation →ₗ[ℤ]
    Module.Dual ℤ (HyperbolicCarrier evaluation) :=
  LinearMap.dualProd ℤ (Perfectification evaluation)

def hyperbolicEmbedding : Perfectification evaluation →ₗ[ℤ]
    HyperbolicCarrier evaluation :=
  LinearMap.inr ℤ (Module.Dual ℤ (Perfectification evaluation))
    (Perfectification evaluation)

def canonicalAmbientMap : C →ₗ[ℤ] HyperbolicCarrier evaluation :=
  (hyperbolicEmbedding evaluation).comp (canonicalMap evaluation)

theorem hyperbolicEmbedding_injective :
    Function.Injective (hyperbolicEmbedding evaluation) :=
  LinearMap.inr_injective

theorem hyperbolicCarrier_map_universal
    {A : Type*} [AddCommGroup A]
    (left : Module.Dual ℤ (Perfectification evaluation) →ₗ[ℤ] A)
    (right : Perfectification evaluation →ₗ[ℤ] A) :
    ∃! map : HyperbolicCarrier evaluation →ₗ[ℤ] A,
      map.comp (LinearMap.inl ℤ
        (Module.Dual ℤ (Perfectification evaluation))
        (Perfectification evaluation)) = left ∧
      map.comp (hyperbolicEmbedding evaluation) = right := by
  refine ⟨left.coprod right, ⟨LinearMap.coprod_inl left right,
    LinearMap.coprod_inr left right⟩, ?_⟩
  intro other equations
  calc
    other = (other.comp (LinearMap.inl ℤ
      (Module.Dual ℤ (Perfectification evaluation))
      (Perfectification evaluation))).coprod
        (other.comp (hyperbolicEmbedding evaluation)) := by
          symm
          exact LinearMap.coprod_comp_inl_inr other
    _ = left.coprod right := by rw [equations.1, equations.2]

@[simp] theorem canonicalAmbientMap_apply (value : C) :
    canonicalAmbientMap evaluation value =
      (0, canonicalMap evaluation value) :=
  rfl

/-! The hyperbolic pairing is genuinely perfect once the source has generated
finite-free evidence.  The proof is the standard product-dual calculation;
no chosen basis or determinant frame is exposed. -/

set_option backward.isDefEq.respectTransparency false in
theorem hyperbolicPairing_bijective
    (free : Module.Free ℤ (Perfectification evaluation))
    (finite : Module.Finite ℤ (Perfectification evaluation)) :
    Function.Bijective (hyperbolicPairing evaluation) := by
  letI : Module.Free ℤ (Perfectification evaluation) := free
  letI : Module.Finite ℤ (Perfectification evaluation) := finite
  let e := LinearEquiv.prodComm ℤ _ _ ≪≫ₗ
    Module.dualProdDualEquivDual ℤ
      (Module.Dual ℤ (Perfectification evaluation))
      (Perfectification evaluation)
  let h_d := e.symm.toLinearMap.comp (hyperbolicPairing evaluation)
  have h_d_eq : h_d =
      (LinearMap.id : Module.Dual ℤ (Perfectification evaluation) →ₗ[ℤ]
        Module.Dual ℤ (Perfectification evaluation)).prodMap
        (Module.Dual.eval ℤ (Perfectification evaluation)) := by
    refine LinearMap.ext fun x => Prod.ext ?_ ?_
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp [hyperbolicPairing, LinearMap.dualProd]
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp [hyperbolicPairing, LinearMap.dualProd]
  have h_d_bij : Function.Bijective h_d := by
    rw [h_d_eq]
    exact Function.Bijective.prodMap Function.bijective_id
      (Module.bijective_dual_eval ℤ (Perfectification evaluation))
  exact (Function.Bijective.of_comp_iff' e.symm.bijective
    (hyperbolicPairing evaluation)).mp h_d_bij

noncomputable def hyperbolicPerfectEquivalence
    (free : Module.Free ℤ (Perfectification evaluation))
    (finite : Module.Finite ℤ (Perfectification evaluation)) :
    HyperbolicCarrier evaluation ≃ₗ[ℤ]
      Module.Dual ℤ (HyperbolicCarrier evaluation) := by
  letI : Module.Free ℤ (Perfectification evaluation) := free
  letI : Module.Finite ℤ (Perfectification evaluation) := finite
  exact LinearEquiv.ofBijective (hyperbolicPairing evaluation)
    (hyperbolicPairing_bijective evaluation free finite)

/-! ## Total ambient disposition -/

inductive PerfectAmbientExtensionDisposition : Type (max c d + 2) where
  | generated
      (free : Module.Free ℤ (Perfectification evaluation))
      (finite : Module.Finite ℤ (Perfectification evaluation))
      (equivalence : HyperbolicCarrier evaluation ≃ₗ[ℤ]
        Module.Dual ℤ (HyperbolicCarrier evaluation))
  | finiteNonfree
      (finite : Module.Finite ℤ (Perfectification evaluation))
      (notFree : ¬ Module.Free ℤ (Perfectification evaluation))
  | representationResidual
      (notFinite : ¬ Module.Finite ℤ (Perfectification evaluation))

noncomputable def settlePerfectAmbientExtension :
    PerfectAmbientExtensionDisposition evaluation := by
  classical
  by_cases finite : Module.Finite ℤ (Perfectification evaluation)
  · by_cases free : Module.Free ℤ (Perfectification evaluation)
    · exact .generated free finite
        (hyperbolicPerfectEquivalence evaluation free finite)
    · exact .finiteNonfree finite free
  · exact .representationResidual finite

theorem perfectAmbientExtension_total :
    Nonempty (PerfectAmbientExtensionDisposition evaluation) :=
  ⟨settlePerfectAmbientExtension evaluation⟩

theorem generated_ambient_is_perfect
    (free : Module.Free ℤ (Perfectification evaluation))
    (finite : Module.Finite ℤ (Perfectification evaluation)) :
    ∃ equivalence : HyperbolicCarrier evaluation ≃ₗ[ℤ]
        Module.Dual ℤ (HyperbolicCarrier evaluation),
      settlePerfectAmbientExtension evaluation =
        .generated free finite equivalence := by
  refine ⟨hyperbolicPerfectEquivalence evaluation free finite, ?_⟩
  simp [settlePerfectAmbientExtension, free, finite]

end
end SourceGeneratedPerfectAmbient
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
