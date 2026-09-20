import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import H0mework.Realization.Fibres.P560

/-!
# Proposition 561: sigma-zero fibers preserve finite degrees of freedom

P555 gave the zero-fiber `LinearEquiv`.  This file records the numerical
degree-of-freedom consequence:

* the standard carrier and its sigma-zero fiber have the same `finrank`;
* finite dimensionality of the standard carrier transports to the zero fiber.

This is the finite-dimensional face of the annealing thesis: at `σ = 0`, the
relaxed carrier has no extra physical/mathematical degrees of freedom hidden
in its headroom coordinate.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Finrank and finite-dimensional transport -/

/-- THEOREM 1: the sigma-zero fiber has exactly the same finrank as the
standard carrier. -/
theorem sigmaZero_finrank_eq
    (K : Type u) [Zero K] (𝕜 : Type*) [DivisionRing 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    Module.finrank 𝕜 (SigmaRelaxedObject K X H (0 : K)) =
      Module.finrank 𝕜 X := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  exact (sigmaZeroRelaxedLinearEquiv K 𝕜 X H).finrank_eq

/-- THEOREM 2: finite dimensionality of the standard carrier transports to the
sigma-zero fiber. -/
theorem sigmaZero_finiteDimensional_of_standard
    (K : Type u) [Zero K] (𝕜 : Type*) [DivisionRing 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X]
    [FiniteDimensional 𝕜 X] :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    FiniteDimensional 𝕜 (SigmaRelaxedObject K X H (0 : K)) := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  exact FiniteDimensional.of_injective
    (sigmaZeroRelaxedLinearEquiv K 𝕜 X H).toLinearMap
    (sigmaZeroRelaxedLinearEquiv K 𝕜 X H).injective

/-- A compact certificate that the zero fiber preserves finite-dimensional
degree counts. -/
structure SigmaZeroFiniteDofCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [DivisionRing 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X] where
  linear_equiv : by
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    exact SigmaRelaxedObject K X H (0 : K) ≃ₗ[𝕜] X
  finrank_eq :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    Module.finrank 𝕜 (SigmaRelaxedObject K X H (0 : K)) =
      Module.finrank 𝕜 X
  finite_dimensional_of_standard :
    FiniteDimensional 𝕜 X ->
      by
        letI := sigmaZeroRelaxedAddCommGroupInst K X H
        letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
        exact FiniteDimensional 𝕜 (SigmaRelaxedObject K X H (0 : K))

/-- THEOREM 3: the canonical finite-degree-of-freedom certificate. -/
def sigmaZeroFiniteDofCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [DivisionRing 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X] :
    SigmaZeroFiniteDofCertificate K 𝕜 X H where
  linear_equiv := sigmaZeroRelaxedLinearEquiv K 𝕜 X H
  finrank_eq := sigmaZero_finrank_eq K 𝕜 X H
  finite_dimensional_of_standard := by
    intro h
    letI := h
    exact sigmaZero_finiteDimensional_of_standard K 𝕜 X H


end AffineRelaxation
end SaturationMonoid
