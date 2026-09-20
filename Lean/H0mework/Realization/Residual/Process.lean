import H0mework.Realization.Residual.Algebra

/-!
# Effective residual process kernel

`ResidualTransportCore` proves the linear-carrier theorem. This module supplies
the Mathlib semantic front door independently of the historical Proposition
numbering:

an effective process is exactly a state update whose residual is transported
by a keep operator.

All trace/split/fixed/energy readings are inherited from the residual transport
core. Projection into historical residual-carrier presentations lives in
`EffectiveResidualProcessProjectionAdapter`. Actual source/event authority is
owned by the separate axiom-free constructive native process kernel.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

open AffineRelaxation

universe u v w

/-! ## Effective process contract -/

/-- An effective residual process: a state update with a produced target,
keep operator, residual map, and the residual transport law. -/
structure EffectiveResidualProcess
    (K E State : Type*) [Field K] [AddCommGroup E] [Module K E] where
  target : E
  keep : E →ₗ[K] E
  residual : State -> E
  update : State -> State
  residual_transport_law :
    ∀ s : State, residual (update s) = keep (residual s)

/-- THEOREM 6: every effective process splits the current residual into
the next residual plus the forced trace. -/
theorem effectiveProcess_residual_eq_next_residual_add_trace
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) (s : State) :
    P.residual s =
      P.residual (P.update s) +
        linearResidualTrace P.keep (P.residual s) := by
  calc
    P.residual s =
        P.keep (P.residual s) +
          linearResidualTrace P.keep (P.residual s) := by
      exact residualTransportCore_residual_split P.keep (P.residual s)
    _ =
        P.residual (P.update s) +
          linearResidualTrace P.keep (P.residual s) := by
      rw [P.residual_transport_law s]

/-- THEOREM 7: the trace component is uniquely forced by the effective
process split. -/
theorem effectiveProcess_trace_unique
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) (s : State) (trace : E) :
    P.residual s = P.residual (P.update s) + trace ↔
      trace = linearResidualTrace P.keep (P.residual s) := by
  rw [P.residual_transport_law s]
  exact residualTransportCore_trace_unique P.keep (P.residual s) trace

/-- THEOREM 8: if the effective process is active and the energy readout is
positive-definite, fixedness, zero residual, zero trace, and zero energy are
one predicate. -/
theorem effectiveProcess_fixed_iff_zero_residual_trace_energy
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State)
    (energy : E -> ℝ)
    (hactive : ResidualTransportActive P.keep)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    (s : State) :
    ResidualTransportFixed P.keep (P.residual s) ↔
      P.residual s = 0 ∧
        linearResidualTrace P.keep (P.residual s) = 0 ∧
          energy (P.residual s) = 0 :=
  residualTransportCore_fixed_iff_zero_residual_trace_energy
    P.keep energy hactive henergy (P.residual s)

end ResidualProjection
end SaturationMonoid
