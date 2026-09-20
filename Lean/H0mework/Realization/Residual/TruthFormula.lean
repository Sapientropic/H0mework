import H0mework.Realization.Residual.Primitive

/-!
# Truth formula core

This is the small theorem at the bottom of the Mathlib residual-algebra layer.
It is not a root authority source; the axiom-free actual producer lives in
`ConstructiveNativeResidualGenerationKernel`.

The primitive object is a residual `r` transported by a keep operator `K`.
The trace is not an extra datum: it is forced as the complementary residual

`trace = (I - K) r = r - K r`.

Hence every active residual transport has one zero condition, read in four
ways:

`fixed <-> residual = 0 <-> trace = 0 <-> energy = 0`.

The scalar chart is the familiar affine saturation display

`r = (1 - sigma) • r + sigma • r`

and

`X' = X + sigma • (T - X)`.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

/-! ## Residual split and trace uniqueness -/

/-- THEOREM 1: the core residual split, in the exact requested orientation:
`r = K r + (I - K) r`. -/
theorem truthFormula_residual_split
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (r : E) :
    r = keep r + linearResidualTrace keep r :=
  residual_eq_linearKeep_add_trace keep r

/-- THEOREM 2: a trace satisfying the residual split is unique.  This pins
`trace` to `(I - K) r`, rather than letting it be an independent bookkeeping
field. -/
theorem truthFormula_trace_unique
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (r trace : E) :
    r = keep r + trace ↔ trace = linearResidualTrace keep r := by
  constructor
  · intro hsplit
    dsimp [linearResidualTrace]
    calc
      trace = (keep r + trace) - keep r := by abel
      _ = r - keep r := by rw [← hsplit]
  · intro htrace
    rw [htrace]
    exact truthFormula_residual_split keep r

/-- THEOREM 3: one-way trace uniqueness, convenient for producer proofs. -/
theorem truthFormula_trace_eq_of_split
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (r trace : E)
    (hsplit : r = keep r + trace) :
    trace = linearResidualTrace keep r :=
  (truthFormula_trace_unique keep r trace).mp hsplit

/-! ## Active transport: fixed / zero / trace / energy collapse -/

/-- The root equivalence package: for an active keep operator and a
positive-definite energy readout, fixedness, zero residual, zero trace, and
zero energy are the same predicate. -/
structure TruthFormulaCoreEquivalence
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (energy : E -> ℝ) (r : E) : Prop where
  fixed_iff_zero_residual :
    ResidualTransportFixed keep r ↔ r = 0
  zero_residual_iff_zero_trace :
    r = 0 ↔ linearResidualTrace keep r = 0
  zero_residual_iff_zero_energy :
    r = 0 ↔ energy r = 0
  zero_trace_iff_zero_energy :
    linearResidualTrace keep r = 0 ↔ energy r = 0
  fixed_iff_zero_trace :
    ResidualTransportFixed keep r ↔ linearResidualTrace keep r = 0
  fixed_iff_zero_energy :
    ResidualTransportFixed keep r ↔ energy r = 0

/-- THEOREM 4: active residual transport proves the whole four-way collapse
at once. -/
theorem truthFormula_core_equivalence
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (energy : E -> ℝ)
    (hactive : ResidualTransportActive keep)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    (r : E) :
    TruthFormulaCoreEquivalence keep energy r where
  fixed_iff_zero_residual :=
    residualTransport_fixed_iff_zero_residual keep hactive r
  zero_residual_iff_zero_trace :=
    (residualTransport_fixed_iff_zero_residual keep hactive r).symm.trans
      (residualTransport_fixed_iff_zero_trace keep hactive r)
  zero_residual_iff_zero_energy :=
    (henergy r).symm
  zero_trace_iff_zero_energy :=
    residualTransport_zero_trace_iff_zero_energy keep energy hactive henergy r
  fixed_iff_zero_trace :=
    residualTransport_fixed_iff_zero_trace keep hactive r
  fixed_iff_zero_energy :=
    residualTransport_fixed_iff_zero_energy keep energy hactive henergy r

/-- THEOREM 5: the same collapse as one compact predicate:
fixed iff all three zero readouts hold. -/
theorem truthFormula_fixed_iff_zero_residual_trace_energy
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (energy : E -> ℝ)
    (hactive : ResidualTransportActive keep)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    (r : E) :
    ResidualTransportFixed keep r ↔
      r = 0 ∧ linearResidualTrace keep r = 0 ∧ energy r = 0 := by
  constructor
  · intro hfixed
    have hz :
        r = 0 :=
      (residualTransport_fixed_iff_zero_residual keep hactive r).mp hfixed
    have ht :
        linearResidualTrace keep r = 0 :=
      (residualTransport_fixed_iff_zero_trace keep hactive r).mp hfixed
    have hE :
        energy r = 0 :=
      (residualTransport_fixed_iff_zero_energy keep energy hactive henergy r).mp
        hfixed
    exact ⟨hz, ht, hE⟩
  · intro hzeros
    exact
      (residualTransport_fixed_iff_zero_residual keep hactive r).mpr
        hzeros.1

/-! ## Scalar affine chart -/

/-- THEOREM 6: scalar residual split:
`r = (1 - sigma) r + sigma r`. -/
theorem truthFormula_scalar_residual_split
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) :
    r = (1 - sigma) • r + sigma • r := by
  module

/-- THEOREM 7: in the scalar chart, the forced trace is exactly
`sigma • r`. -/
theorem truthFormula_scalar_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) :
    linearResidualTrace (scalarKeepLinearMap (K := K) (E := E) sigma) r =
      sigma • r := by
  dsimp [linearResidualTrace, scalarKeepLinearMap]
  module

/-- THEOREM 8: scalar residual transport is the affine update
`X' = X + sigma • (T - X)`. -/
theorem truthFormula_scalar_affine_update
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) :
    residualTransportUpdate
        (fun r : E => scalarKeepLinearMap (K := K) (E := E) sigma r)
        target x =
      x + sigma • (target - x) := by
  simpa [relaxModule]
    using scalar_linearResidualTransportUpdate_eq_relaxModule
      (K := K) (E := E) target sigma x

/-- THEOREM 9: at scalar target `1`, the affine chart is exactly
`bumpSatField`. -/
theorem truthFormula_scalar_target_one_bumpSat
    {K : Type*} [Field K] (h sigma : K) :
    residualTransportUpdate
        (fun r : K => scalarKeepLinearMap (K := K) (E := K) sigma r)
        1 h =
      bumpSatField h sigma := by
  dsimp [residualTransportUpdate, scalarKeepLinearMap, bumpSatField]

/-- THEOREM 10: nonzero scalar rate is active, so the scalar chart inherits
the full fixed/zero/trace/energy collapse. -/
theorem truthFormula_scalar_core_equivalence
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [NoZeroSMulDivisors K E]
    (sigma : K) (hsigma : sigma ≠ 0)
    (energy : E -> ℝ)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    (r : E) :
    TruthFormulaCoreEquivalence
      (scalarKeepLinearMap (K := K) (E := E) sigma) energy r :=
  truthFormula_core_equivalence
    (scalarKeepLinearMap (K := K) (E := E) sigma) energy
    (scalarKeepLinearMap_active_of_ne_zero (E := E) sigma hsigma)
    henergy r

/-- The core theorem as a reusable certificate. -/
structure TruthFormulaCoreCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  residual_split :
    ∀ keep : E →ₗ[K] E, ∀ r : E,
      r = keep r + linearResidualTrace keep r
  trace_unique :
    ∀ keep : E →ₗ[K] E, ∀ r trace : E,
      r = keep r + trace ↔ trace = linearResidualTrace keep r
  active_core_equivalence :
    ∀ keep : E →ₗ[K] E, ∀ energy : E -> ℝ,
      ResidualTransportActive keep ->
        (∀ r : E, energy r = 0 ↔ r = 0) ->
          ∀ r : E, TruthFormulaCoreEquivalence keep energy r
  fixed_iff_all_zero :
    ∀ keep : E →ₗ[K] E, ∀ energy : E -> ℝ,
      ResidualTransportActive keep ->
        (∀ r : E, energy r = 0 ↔ r = 0) ->
          ∀ r : E,
            ResidualTransportFixed keep r ↔
              r = 0 ∧ linearResidualTrace keep r = 0 ∧ energy r = 0
  scalar_split :
    ∀ sigma : K, ∀ r : E,
      r = (1 - sigma) • r + sigma • r
  scalar_affine_update :
    ∀ target : E, ∀ sigma : K, ∀ x : E,
      residualTransportUpdate
          (fun r : E => scalarKeepLinearMap (K := K) (E := E) sigma r)
          target x =
        x + sigma • (target - x)

/-- THEOREM 11: canonical truth-formula core certificate. -/
theorem truthFormulaCoreCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    TruthFormulaCoreCertificate K E where
  residual_split := by
    intro keep r
    exact truthFormula_residual_split keep r
  trace_unique := by
    intro keep r trace
    exact truthFormula_trace_unique keep r trace
  active_core_equivalence := by
    intro keep energy hactive henergy r
    exact truthFormula_core_equivalence keep energy hactive henergy r
  fixed_iff_all_zero := by
    intro keep energy hactive henergy r
    exact truthFormula_fixed_iff_zero_residual_trace_energy
      keep energy hactive henergy r
  scalar_split := by
    intro sigma r
    exact truthFormula_scalar_residual_split sigma r
  scalar_affine_update := by
    intro target sigma x
    exact truthFormula_scalar_affine_update target sigma x

end AffineRelaxation
end SaturationMonoid
