import H0mework.Realization.Fibres.P565
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Proposition 566: sigma-zero fibers preserve quotient modules

P563--P565 preserve kernels, ranges, exactness, and chain equations.  This file
pushes the same zero-fiber bridge through quotient modules: quotienting the
sigma-zero fiber by the pullback of a standard submodule is linearly equivalent
to quotienting the standard carrier itself.

This is the quotient-facing spine for gauge reductions, coboundary quotients,
constraint quotients, and cohomology carriers.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Quotient compatibility -/

/-- The zero-fiber quotient by the pullback of a standard submodule is
canonically linearly equivalent to the standard quotient. -/
def sigmaZeroQuotientLinearEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [AddCommGroup X] [Module 𝕜 X]
    (S : Submodule 𝕜 X) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    (SigmaRelaxedObject K X HX (0 : K) ⧸
        S.comap ((sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).toLinearMap)) ≃ₗ[𝕜]
      (X ⧸ S) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  let e := sigmaZeroRelaxedLinearEquiv K 𝕜 X HX
  exact Submodule.Quotient.equiv
    (S.comap (e.toLinearMap)) S e
    (by
      simpa [e] using
        (Submodule.map_comap_eq_of_surjective
          (f := (e.toLinearMap)) e.surjective S))

/-- THEOREM 1: the quotient equivalence sends a zero-fiber quotient class to
the quotient class of its forgetful projection. -/
@[simp] theorem sigmaZeroQuotientLinearEquiv_apply_mk
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [AddCommGroup X] [Module 𝕜 X]
    (S : Submodule 𝕜 X)
    (z : SigmaRelaxedObject K X HX (0 : K)) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    sigmaZeroQuotientLinearEquiv K 𝕜 X HX S
        (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (sigmaZeroForget (K := K) (X := X) (H := HX) z) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  simp [sigmaZeroQuotientLinearEquiv]

/-- THEOREM 2: the inverse quotient equivalence sends a standard quotient
class to the class of its zero-fiber embedding. -/
@[simp] theorem sigmaZeroQuotientLinearEquiv_symm_apply_mk
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [AddCommGroup X] [Module 𝕜 X]
    (S : Submodule 𝕜 X)
    (x : X) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X HX
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
    (sigmaZeroQuotientLinearEquiv K 𝕜 X HX S).symm
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (sigmaZeroEmbed (K := K) (X := X) (H := HX) x) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X HX
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
  simp [sigmaZeroQuotientLinearEquiv]
  have h :
      (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).symm x =
        sigmaZeroEmbed (K := K) (X := X) (H := HX) x := by
    apply (sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).injective
    simp
  simp [h]

/-- A compact certificate bundling quotient-module compatibility at the
sigma-zero fiber. -/
structure SigmaZeroQuotientCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [AddCommGroup X] [Module 𝕜 X] where
  quotient_equiv :
    ∀ (S : Submodule 𝕜 X),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      (SigmaRelaxedObject K X HX (0 : K) ⧸
          S.comap ((sigmaZeroRelaxedLinearEquiv K 𝕜 X HX).toLinearMap)) ≃ₗ[𝕜]
        (X ⧸ S)
  quotient_apply_mk :
    ∀ (S : Submodule 𝕜 X)
      (z : SigmaRelaxedObject K X HX (0 : K)),
      letI := sigmaZeroRelaxedAddCommGroupInst K X HX
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X HX
      quotient_equiv S (Submodule.Quotient.mk z) =
        Submodule.Quotient.mk
          (sigmaZeroForget (K := K) (X := X) (H := HX) z)

/-- DEFINITION 3: the canonical zero-fiber quotient certificate.  This is a
`def`, not a `theorem`, because it packages actual equivalence data. -/
def sigmaZeroQuotientCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Ring 𝕜]
    (X : Type v) (HX : Type w) [Inhabited HX]
    [AddCommGroup X] [Module 𝕜 X] :
    SigmaZeroQuotientCertificate K 𝕜 X HX where
  quotient_equiv := by
    intro S
    exact sigmaZeroQuotientLinearEquiv K 𝕜 X HX S
  quotient_apply_mk := by
    intro S z
    exact sigmaZeroQuotientLinearEquiv_apply_mk K 𝕜 X HX S z


end AffineRelaxation
end SaturationMonoid
