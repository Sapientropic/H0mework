import H0mework.Realization.Relations.P230
import H0mework.Realization.Residual.Primitive

/-!
# Proposition 231: module-valued target-general relaxation

P225 proves the unified scalar law

`x -> x + sigma * (target - x)`.

This file lifts the algebraic spine to any module over a field:

`x -> x + sigma • (target - x)`.

The result is still purely algebraic.  It does not yet prove normed-vector
contraction, complex/unitary physics, tensor geometry, or gauge transport.
It closes the first carrier-generalization step needed by
`unified_equation.md`: the formula is no longer only scalar-valued.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Module-valued relaxation -/

-- `relaxModule` is defined by `ResidualTransportPrimitiveKernel`; this
-- historical proposition retains the richer algebraic readouts.

/-- Module-valued relaxation is an affine combination of the current state and
the target. -/
lemma relaxModule_eq_affine
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) :
    relaxModule target sigma x = (1 - sigma) • x + sigma • target := by
  unfold relaxModule
  module

/-- The residual-to-target vector is multiplied by `1 - sigma`. -/
lemma target_sub_relaxModule
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) :
    target - relaxModule target sigma x = (1 - sigma) • (target - x) := by
  unfold relaxModule
  module

/-! ## Same-target noisy-OR composition -/

/-- Same-target module relaxations compose by the same noisy-OR rate law as the
scalar theorem. -/
theorem relaxModule_compose
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) (sigma1 sigma2 : K) :
    relaxModule target sigma2 (relaxModule target sigma1 x) =
      relaxModule target (satOrField sigma1 sigma2) x := by
  unfold relaxModule satOrField
  module

/-- Same-target module relaxations commute. -/
theorem relaxModule_compose_comm
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) (sigma1 sigma2 : K) :
    relaxModule target sigma2 (relaxModule target sigma1 x) =
      relaxModule target sigma1 (relaxModule target sigma2 x) := by
  unfold relaxModule
  module

/-- Three same-target module relaxations associate by noisy-OR composition. -/
theorem relaxModule_compose_assoc
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) (sigma1 sigma2 sigma3 : K) :
    relaxModule target sigma3
        (relaxModule target sigma2 (relaxModule target sigma1 x)) =
      relaxModule target (satOrField sigma1 (satOrField sigma2 sigma3)) x := by
  unfold relaxModule satOrField
  module

/-! ## Units and absorbing states -/

/-- Rate `0` is a no-op. -/
theorem relaxModule_zero
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) :
    relaxModule target (0 : K) x = x := by
  unfold relaxModule
  simp

/-- Rate `1` jumps directly to the target. -/
theorem relaxModule_one
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) :
    relaxModule target (1 : K) x = target := by
  unfold relaxModule
  simp

/-- The target is an absorbing state for every rate. -/
theorem relaxModule_target_absorbing
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) :
    relaxModule target sigma target = target := by
  unfold relaxModule
  simp

/-! ## Cross-target obstruction -/

/-- The exact module-valued commutator for two target-general relaxations. -/
theorem relaxModule_cross_target_commutator
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target1 target2 x : E) (sigma1 sigma2 : K) :
    relaxModule target2 sigma2 (relaxModule target1 sigma1 x) -
        relaxModule target1 sigma1 (relaxModule target2 sigma2 x) =
      (sigma1 * sigma2) • (target2 - target1) := by
  unfold relaxModule
  module

/-!
  Summary:
  - The unified formula is now certified over arbitrary modules, not just
    scalar fields.
  - Same-target composition remains exactly noisy-OR.
  - Active cross-target steps still carry an obstruction, now as a vector in
    the target carrier: `(sigma1 * sigma2) • (target2 - target1)`.

  Boundary:
  - This is module algebra only.  Normed contraction, complex/unitary
    evolution, tensor geometry, and gauge/target transport remain separate
    proof obligations.
-/


end AffineRelaxation
end SaturationMonoid
