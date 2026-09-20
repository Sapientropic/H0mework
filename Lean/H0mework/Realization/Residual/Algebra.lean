import H0mework.Realization.Residual.TruthFormula

/-!
# Residual transport core

This is the canonical cite path for the framework spine:

`r = K r + (I - K) r`,

`trace = (I - K) r`,

and, for an active/faithful keep operator, the four zero/fixed readings are
one predicate:

`fixed <-> residual = 0 <-> trace = 0 <-> energy = 0`.

The scalar chart is the affine saturation display

`r = (1 - sigma) • r + sigma • r`

and

`X' = X + sigma • (T - X)`.

This file deliberately does not import the Standard Model, Goldbach, SAT, or
Hamiltonian producer layers.  Those are projections of this core, not premises
for it.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

/-! ## Layer 0: residual split -/

/-- Residual split in the requested transport notation:
`r = K r + (I - K) r`. -/
theorem residualTransportCore_residual_split
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (r : E) :
    r = keep r + linearResidualTrace keep r :=
  truthFormula_residual_split keep r

/-- The split pins the trace uniquely to `(I - K) r`; trace is not an
independent bookkeeping field. -/
theorem residualTransportCore_trace_unique
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (r trace : E) :
    r = keep r + trace ↔ trace = linearResidualTrace keep r :=
  truthFormula_trace_unique keep r trace

/-- One-way trace uniqueness, useful when a producer supplies the split. -/
theorem residualTransportCore_trace_eq_of_split
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (r trace : E)
    (hsplit : r = keep r + trace) :
    trace = linearResidualTrace keep r :=
  truthFormula_trace_eq_of_split keep r trace hsplit

/-! ## Layer 1: faithful transport -/

/-- Active/faithful residual transport is exactly the standard kernel condition
`ker(I - K) = 0`. -/
theorem residualTransportCore_active_iff_ker_id_sub_eq_bot
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) :
    ResidualTransportActive keep ↔
      LinearMap.ker ((LinearMap.id : E →ₗ[K] E) - keep) = ⊥ :=
  residualTransportActive_iff_ker_id_sub_eq_bot keep

/-- Active/faithful residual transport collapses fixedness, zero residual,
zero trace, and zero energy into one predicate. -/
theorem residualTransportCore_fixed_iff_zero_residual_trace_energy
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (energy : E -> ℝ)
    (hactive : ResidualTransportActive keep)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    (r : E) :
    ResidualTransportFixed keep r ↔
      r = 0 ∧ linearResidualTrace keep r = 0 ∧ energy r = 0 :=
  truthFormula_fixed_iff_zero_residual_trace_energy
    keep energy hactive henergy r

/-- The same collapse as a structured equivalence package. -/
theorem residualTransportCore_equivalence
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (energy : E -> ℝ)
    (hactive : ResidualTransportActive keep)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    (r : E) :
    TruthFormulaCoreEquivalence keep energy r :=
  truthFormula_core_equivalence keep energy hactive henergy r

/-! ## Layer 1 scalar chart -/

/-- Scalar residual split:
`r = (1 - sigma) • r + sigma • r`. -/
theorem residualTransportCore_scalar_split
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) :
    r = (1 - sigma) • r + sigma • r :=
  truthFormula_scalar_residual_split sigma r

/-- In the scalar chart, the forced trace is exactly `sigma • r`. -/
theorem residualTransportCore_scalar_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) :
    linearResidualTrace (scalarKeepLinearMap (K := K) (E := E) sigma) r =
      sigma • r :=
  truthFormula_scalar_trace sigma r

/-- Scalar residual transport displayed in state coordinates:
`X' = X + sigma • (T - X)`. -/
theorem residualTransportCore_scalar_affine_update
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) :
    residualTransportUpdate
        (fun r : E => scalarKeepLinearMap (K := K) (E := E) sigma r)
        target x =
      x + sigma • (target - x) :=
  truthFormula_scalar_affine_update target sigma x

/-- At scalar target `1`, the affine display is exactly `bumpSatField`. -/
theorem residualTransportCore_target_one_bumpSat
    {K : Type*} [Field K] (h sigma : K) :
    residualTransportUpdate
        (fun r : K => scalarKeepLinearMap (K := K) (E := K) sigma r)
        1 h =
      bumpSatField h sigma :=
  truthFormula_scalar_target_one_bumpSat h sigma

/-- Nonzero scalar rate makes the scalar keep active, so the full core
equivalence applies to the scalar bump/relaxation chart. -/
theorem residualTransportCore_scalar_equivalence
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [NoZeroSMulDivisors K E]
    (sigma : K) (hsigma : sigma ≠ 0)
    (energy : E -> ℝ)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    (r : E) :
    TruthFormulaCoreEquivalence
      (scalarKeepLinearMap (K := K) (E := E) sigma) energy r :=
  truthFormula_scalar_core_equivalence sigma hsigma energy henergy r

/-! ## Certificate -/

/-- The compact residual transport core certificate. -/
structure ResidualTransportCoreCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  active_iff_ker_id_sub_eq_bot :
    ∀ keep : E →ₗ[K] E,
      ResidualTransportActive keep ↔
        LinearMap.ker ((LinearMap.id : E →ₗ[K] E) - keep) = ⊥
  residual_split :
    ∀ keep : E →ₗ[K] E, ∀ r : E,
      r = keep r + linearResidualTrace keep r
  trace_unique :
    ∀ keep : E →ₗ[K] E, ∀ r trace : E,
      r = keep r + trace ↔ trace = linearResidualTrace keep r
  active_fixed_zero_trace_energy :
    ∀ keep : E →ₗ[K] E, ∀ energy : E -> ℝ,
      ResidualTransportActive keep ->
        (∀ r : E, energy r = 0 ↔ r = 0) ->
          ∀ r : E,
            ResidualTransportFixed keep r ↔
              r = 0 ∧ linearResidualTrace keep r = 0 ∧ energy r = 0
  scalar_split :
    ∀ sigma : K, ∀ r : E,
      r = (1 - sigma) • r + sigma • r
  scalar_trace :
    ∀ sigma : K, ∀ r : E,
      linearResidualTrace (scalarKeepLinearMap (K := K) (E := E) sigma) r =
        sigma • r
  scalar_affine_update :
    ∀ target : E, ∀ sigma : K, ∀ x : E,
      residualTransportUpdate
          (fun r : E => scalarKeepLinearMap (K := K) (E := E) sigma r)
          target x =
        x + sigma • (target - x)

/-- Canonical residual transport core certificate. -/
theorem residualTransportCoreCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ResidualTransportCoreCertificate K E where
  active_iff_ker_id_sub_eq_bot := by
    intro keep
    exact residualTransportCore_active_iff_ker_id_sub_eq_bot keep
  residual_split := by
    intro keep r
    exact residualTransportCore_residual_split keep r
  trace_unique := by
    intro keep r trace
    exact residualTransportCore_trace_unique keep r trace
  active_fixed_zero_trace_energy := by
    intro keep energy hactive henergy r
    exact residualTransportCore_fixed_iff_zero_residual_trace_energy
      keep energy hactive henergy r
  scalar_split := by
    intro sigma r
    exact residualTransportCore_scalar_split sigma r
  scalar_trace := by
    intro sigma r
    exact residualTransportCore_scalar_trace sigma r
  scalar_affine_update := by
    intro target sigma x
    exact residualTransportCore_scalar_affine_update target sigma x

end AffineRelaxation
end SaturationMonoid
