import Mathlib.LinearAlgebra.Contraction
import H0mework.Realization.FibreLinear.P559

/-!
# Proposition 560: sigma-zero fibers preserve algebraic duals and evaluation

P559 showed that composite algebraic tensor carriers anneal at `σ = 0`.
This file adds the state/observable face:

* the algebraic dual of a standard carrier is linearly equivalent to the dual
  of its sigma-zero fiber;
* evaluation is strictly the same scalar after the forgetful projection;
* the tensor contraction `Dual X ⊗ X -> 𝕜` commutes on pure tensors.

The scalar target is intentionally not relaxed here.  Observations are read in
the original coefficient field; only the state carrier carries a zero-fiber
headroom coordinate.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Algebraic dual compatibility at the zero fiber -/

/-- The algebraic dual of a sigma-zero fiber.  Naming this carrier keeps
the required transported module instances local and avoids hiding the fact that
it is still just a linear-functional space. -/
abbrev SigmaZeroDualCarrier
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X] : Type _ := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  exact Module.Dual 𝕜 (SigmaRelaxedObject K X H (0 : K))

/-- THEOREM 1: duals of a standard carrier and its sigma-zero fiber are
linearly equivalent by contravariant transport along the zero-fiber
`LinearEquiv`. -/
def sigmaZeroDualLinearEquiv
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X] : by
      letI := sigmaZeroRelaxedAddCommMonoidInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      exact
        Module.Dual 𝕜 X ≃ₗ[𝕜] SigmaZeroDualCarrier K 𝕜 X H := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  exact (sigmaZeroRelaxedLinearEquiv K 𝕜 X H).dualMap

/-- THEOREM 2: transporting a functional to the zero fiber evaluates by first
forgetting the zero-fiber headroom. -/
@[simp] theorem sigmaZeroDualLinearEquiv_apply
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X]
    (φ : Module.Dual 𝕜 X)
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    sigmaZeroDualLinearEquiv K 𝕜 X H φ z =
      φ (sigmaZeroForget (K := K) (X := X) (H := H) z) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  rfl

/-- THEOREM 3: descending a zero-fiber functional evaluates a standard point by
first embedding it into the zero fiber. -/
@[simp] theorem sigmaZeroDualLinearEquiv_symm_apply
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X]
    (ψ : SigmaZeroDualCarrier K 𝕜 X H)
    (x : X) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    (sigmaZeroDualLinearEquiv K 𝕜 X H).symm ψ x =
      ψ (sigmaZeroEmbed (K := K) (X := X) (H := H) x) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  rfl

/-- THEOREM 4: contraction of a transported dual with a zero-fiber state is
the same scalar as contraction after forgetting the state. -/
@[simp] theorem sigmaZero_contractLeft_tmul
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X]
    (φ : Module.Dual 𝕜 X)
    (z : SigmaRelaxedObject K X H (0 : K)) :
    letI := sigmaZeroRelaxedAddCommMonoidInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    contractLeft 𝕜 (SigmaRelaxedObject K X H (0 : K))
        ((sigmaZeroDualLinearEquiv K 𝕜 X H φ) ⊗ₜ[𝕜] z) =
      contractLeft 𝕜 X
        (φ ⊗ₜ[𝕜] sigmaZeroForget (K := K) (X := X) (H := H) z) := by
  letI := sigmaZeroRelaxedAddCommMonoidInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  simp [contractLeft_apply]

/-- A compact certificate bundling dual transport and scalar evaluation
compatibility at the zero fiber. -/
structure SigmaZeroDualPairingCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X] where
  dual_linear_equiv : by
    letI := sigmaZeroRelaxedAddCommMonoidInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    exact
      Module.Dual 𝕜 X ≃ₗ[𝕜] SigmaZeroDualCarrier K 𝕜 X H
  evaluation_forget :
    ∀ (φ : Module.Dual 𝕜 X)
      (z : SigmaRelaxedObject K X H (0 : K)),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      dual_linear_equiv φ z =
        φ (sigmaZeroForget (K := K) (X := X) (H := H) z)
  evaluation_embed :
    ∀ (ψ : SigmaZeroDualCarrier K 𝕜 X H) (x : X),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      dual_linear_equiv.symm ψ x =
        ψ (sigmaZeroEmbed (K := K) (X := X) (H := H) x)
  contraction_forget :
    ∀ (φ : Module.Dual 𝕜 X)
      (z : SigmaRelaxedObject K X H (0 : K)),
      letI := sigmaZeroRelaxedAddCommMonoidInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      contractLeft 𝕜 (SigmaRelaxedObject K X H (0 : K))
          ((dual_linear_equiv φ) ⊗ₜ[𝕜] z) =
        contractLeft 𝕜 X
          (φ ⊗ₜ[𝕜] sigmaZeroForget (K := K) (X := X) (H := H) z)

/-- THEOREM 5: the canonical zero-fiber dual/evaluation certificate. -/
def sigmaZeroDualPairingCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [CommSemiring 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommMonoid X] [Module 𝕜 X] :
    SigmaZeroDualPairingCertificate K 𝕜 X H where
  dual_linear_equiv := sigmaZeroDualLinearEquiv K 𝕜 X H
  evaluation_forget := by
    intro φ z
    exact sigmaZeroDualLinearEquiv_apply K 𝕜 X H φ z
  evaluation_embed := by
    intro ψ x
    exact sigmaZeroDualLinearEquiv_symm_apply K 𝕜 X H ψ x
  contraction_forget := by
    intro φ z
    exact sigmaZero_contractLeft_tmul K 𝕜 X H φ z


end AffineRelaxation
end SaturationMonoid
