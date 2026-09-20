import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import H0mework.Realization.Fibres.P561

/-!
# Proposition 562: sigma-zero lifted endomorphisms preserve spectral invariants

P557 lifted standard endomorphisms to sigma-zero fibers by conjugating through
the zero-fiber `LinearEquiv`.  This file records the invariant consequences:

* determinant is preserved;
* trace is preserved;
* characteristic polynomial is preserved.

These are the finite-operator readouts behind many physical quantities.  At
the annealed `σ = 0` face, adding the relaxed headroom coordinate does not
change the operator's determinant, trace, or characteristic polynomial.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v w

/-! ## Endomorphism invariants under zero-fiber lift -/

/-- THEOREM 1: lifting an endomorphism to the sigma-zero fiber preserves its
determinant. -/
theorem sigmaZeroLiftLinearMap_det
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X]
    (f : X →ₗ[𝕜] X) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    LinearMap.det (sigmaZeroLiftLinearMap K 𝕜 X X H H f) =
      LinearMap.det f := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  let e := sigmaZeroRelaxedLinearEquiv K 𝕜 X H
  change LinearMap.det (((e.symm : X →ₗ[𝕜] SigmaRelaxedObject K X H (0 : K))).comp
      (f.comp (e : SigmaRelaxedObject K X H (0 : K) →ₗ[𝕜] X))) =
    LinearMap.det f
  simpa [LinearMap.comp_assoc] using LinearMap.det_conj f e.symm

/-- THEOREM 2: lifting an endomorphism to the sigma-zero fiber preserves its
trace. -/
theorem sigmaZeroLiftLinearMap_trace
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
    (f : X →ₗ[𝕜] X) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    LinearMap.trace 𝕜 (SigmaRelaxedObject K X H (0 : K))
        (sigmaZeroLiftLinearMap K 𝕜 X X H H f) =
      LinearMap.trace 𝕜 X f := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  letI : FiniteDimensional 𝕜 (SigmaRelaxedObject K X H (0 : K)) :=
    sigmaZero_finiteDimensional_of_standard K 𝕜 X H
  let e := sigmaZeroRelaxedLinearEquiv K 𝕜 X H
  simpa [sigmaZeroLiftLinearMap, LinearEquiv.conj_apply, LinearMap.comp_assoc] using
    LinearMap.trace_conj' f e.symm

/-- THEOREM 3: lifting an endomorphism to the sigma-zero fiber preserves its
characteristic polynomial. -/
@[simp] theorem sigmaZeroLiftLinearMap_charpoly
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X]
    (f : X →ₗ[𝕜] X) :
    letI := sigmaZeroRelaxedAddCommGroupInst K X H
    letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
    letI := sigmaZero_finiteDimensional_of_standard K 𝕜 X H
    LinearMap.charpoly (sigmaZeroLiftLinearMap K 𝕜 X X H H f) =
      LinearMap.charpoly f := by
  letI := sigmaZeroRelaxedAddCommGroupInst K X H
  letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
  letI : FiniteDimensional 𝕜 (SigmaRelaxedObject K X H (0 : K)) :=
    sigmaZero_finiteDimensional_of_standard K 𝕜 X H
  let e := sigmaZeroRelaxedLinearEquiv K 𝕜 X H
  simpa [sigmaZeroLiftLinearMap, LinearEquiv.conj_apply, LinearMap.comp_assoc] using
    (LinearEquiv.charpoly_conj e.symm f)

/-- A compact certificate bundling determinant, trace, and characteristic
polynomial invariance for zero-fiber lifted endomorphisms. -/
structure SigmaZeroEndomorphismInvariantCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X] where
  determinant :
    ∀ f : X →ₗ[𝕜] X,
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      LinearMap.det (sigmaZeroLiftLinearMap K 𝕜 X X H H f) =
        LinearMap.det f
  trace :
    ∀ f : X →ₗ[𝕜] X,
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      LinearMap.trace 𝕜 (SigmaRelaxedObject K X H (0 : K))
          (sigmaZeroLiftLinearMap K 𝕜 X X H H f) =
        LinearMap.trace 𝕜 X f
  charpoly :
    ∀ f : X →ₗ[𝕜] X,
      letI := sigmaZeroRelaxedAddCommGroupInst K X H
      letI := sigmaZeroRelaxedModuleInst K 𝕜 X H
      letI := sigmaZero_finiteDimensional_of_standard K 𝕜 X H
      LinearMap.charpoly (sigmaZeroLiftLinearMap K 𝕜 X X H H f) =
        LinearMap.charpoly f

/-- THEOREM 4: the canonical zero-fiber endomorphism invariant certificate. -/
theorem sigmaZeroEndomorphismInvariantCertificate
    (K : Type u) [Zero K] (𝕜 : Type*) [Field 𝕜]
    (X : Type v) (H : Type w) [Inhabited H]
    [AddCommGroup X] [Module 𝕜 X] [FiniteDimensional 𝕜 X] :
    SigmaZeroEndomorphismInvariantCertificate K 𝕜 X H where
  determinant := by
    intro f
    exact sigmaZeroLiftLinearMap_det K 𝕜 X H f
  trace := by
    intro f
    exact sigmaZeroLiftLinearMap_trace K 𝕜 X H f
  charpoly := by
    intro f
    exact sigmaZeroLiftLinearMap_charpoly K 𝕜 X H f


end AffineRelaxation
end SaturationMonoid
