import H0mework.Physics.JointSources.P744
import H0mework.Realization.Residual.Primitive

/-!
# Proposition 745: residual transport principle

P743 identifies the first formula as the conserved split

`r = (1 - sigma) • r + sigma • r`.

This file removes the last scalar accident from that statement.  The primitive
object is a keep operator `K` on residuals:

`r' = K r`.

The trace is not another primitive; it is the complementary residual

`r - K r`.

Thus every linear residual transport carries its own keep/trace conservation
law.  The familiar affine relaxation

`x ↦ x + sigma • (target - x)`

is recovered as the scalar slice `K = (1 - sigma) • Id`.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

/-! ## Operator-valued keep/trace split -/

-- The forced trace and conserved split are defined in
-- `ResidualTransportPrimitiveKernel`.  The remaining declarations are the
-- historical state-space, composition, and scalar-presentation readouts.

/-! ## State-space reading -/

/-- THEOREM 3: the target residual of the transported state is exactly `keep r`. -/
theorem target_sub_linearResidualTransportUpdate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (keep : E →ₗ[K] E) (x : E) :
    target - residualTransportUpdate (fun r : E => keep r) target x =
      keep (target - x) := by
  exact residualTransportUpdate_residual (fun r : E => keep r) target x

/-- THEOREM 4: the state displacement is exactly the complementary trace. -/
theorem linearResidualTransportDelta_eq_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (keep : E →ₗ[K] E) (x : E) :
    residualTransportUpdate (fun r : E => keep r) target x - x =
      linearResidualTrace keep (target - x) := by
  dsimp [residualTransportUpdate, linearResidualTrace]
  abel

/-- THEOREM 5: any update with the same residual transport law is forced to be
the canonical residual-transport update. -/
theorem update_eq_linearResidualTransportUpdate_of_residual_law
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (keep : E →ₗ[K] E) (update : E -> E)
    (h : ∀ x : E, target - update x = keep (target - x)) :
    ∀ x : E, update x = residualTransportUpdate (fun r : E => keep r) target x := by
  intro x
  calc
    update x = target - (target - update x) := by abel
    _ = target - keep (target - x) := by rw [h x]
    _ = residualTransportUpdate (fun r : E => keep r) target x := rfl

/-- THEOREM 6: any update with the same trace law is forced to be the canonical
residual-transport update. -/
theorem update_eq_linearResidualTransportUpdate_of_trace_law
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (keep : E →ₗ[K] E) (update : E -> E)
    (h : ∀ x : E, update x - x = linearResidualTrace keep (target - x)) :
    ∀ x : E, update x = residualTransportUpdate (fun r : E => keep r) target x := by
  intro x
  calc
    update x = x + (update x - x) := by abel
    _ = x + linearResidualTrace keep (target - x) := by rw [h x]
    _ = residualTransportUpdate (fun r : E => keep r) target x := by
      dsimp [residualTransportUpdate, linearResidualTrace]
      abel

/-! ## Composition reading -/

/-- THEOREM 7: residual transport composition is operator composition. -/
theorem linearResidualTransportUpdate_compose
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (keep₂ keep₁ : E →ₗ[K] E) (x : E) :
    residualTransportUpdate (fun r : E => keep₂ r) target
        (residualTransportUpdate (fun r : E => keep₁ r) target x) =
      residualTransportUpdate (fun r : E => (keep₂.comp keep₁) r) target x := by
  simpa [Function.comp_def] using
    residualTransportUpdate_compose
      (fun r : E => keep₁ r) (fun r : E => keep₂ r) target x

/-! ## Scalar slice recovers affine relaxation -/

-- `scalarKeepLinearMap` and its affine-update theorem are primitive-kernel
-- declarations; the P745 names below relate that chart to historical P743
-- presentations and composition laws.

/-- THEOREM 10: the scalar operator trace is the P743 `residualTrace`. -/
theorem scalar_linearResidualTrace_eq_residualTrace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) (r : E) :
    linearResidualTrace (scalarKeepLinearMap (K := K) (E := E) sigma) r =
      residualTrace sigma r := by
  dsimp [linearResidualTrace, scalarKeepLinearMap, residualTrace]
  module

/-- THEOREM 11: the scalar operator composition recovers noisy-OR. -/
theorem scalarKeepLinearMap_comp
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma₂ sigma₁ : K) :
    (scalarKeepLinearMap (K := K) (E := E) sigma₂).comp
        (scalarKeepLinearMap (K := K) (E := E) sigma₁) =
      scalarKeepLinearMap (K := K) (E := E) (satOrField sigma₁ sigma₂) := by
  ext r
  dsimp [scalarKeepLinearMap, satOrField]
  module

/-! ## Packaged certificate -/

/-- P745 certificate: every linear effective process is a residual transport;
`relaxModule` is exactly its scalar keep-operator slice. -/
structure LinearResidualTransportPrincipleCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  operator_split_conserved :
    ∀ keep : E →ₗ[K] E, ∀ r : E,
      r = keep r + linearResidualTrace keep r
  residual_transport_law :
    ∀ target : E, ∀ keep : E →ₗ[K] E, ∀ x : E,
      target - residualTransportUpdate (fun r : E => keep r) target x =
        keep (target - x)
  trace_displacement_law :
    ∀ target : E, ∀ keep : E →ₗ[K] E, ∀ x : E,
      residualTransportUpdate (fun r : E => keep r) target x - x =
        linearResidualTrace keep (target - x)
  residual_law_unique :
    ∀ target : E, ∀ keep : E →ₗ[K] E, ∀ update : E -> E,
      (∀ x : E, target - update x = keep (target - x)) ->
        ∀ x : E, update x =
          residualTransportUpdate (fun r : E => keep r) target x
  trace_law_unique :
    ∀ target : E, ∀ keep : E →ₗ[K] E, ∀ update : E -> E,
      (∀ x : E, update x - x = linearResidualTrace keep (target - x)) ->
        ∀ x : E, update x =
          residualTransportUpdate (fun r : E => keep r) target x
  operator_composition :
    ∀ target : E, ∀ keep₂ keep₁ : E →ₗ[K] E, ∀ x : E,
      residualTransportUpdate (fun r : E => keep₂ r) target
          (residualTransportUpdate (fun r : E => keep₁ r) target x) =
        residualTransportUpdate (fun r : E => (keep₂.comp keep₁) r) target x
  two_step_trace :
    ∀ keep₂ keep₁ : E →ₗ[K] E, ∀ r : E,
      linearResidualTrace keep₁ r +
          linearResidualTrace keep₂ (keep₁ r) =
        linearResidualTrace (keep₂.comp keep₁) r
  scalar_slice_is_relaxModule :
    ∀ target : E, ∀ sigma : K, ∀ x : E,
      residualTransportUpdate
          (fun r : E => scalarKeepLinearMap (K := K) (E := E) sigma r) target x =
        relaxModule target sigma x
  scalar_trace_is_p743_trace :
    ∀ sigma : K, ∀ r : E,
      linearResidualTrace (scalarKeepLinearMap (K := K) (E := E) sigma) r =
        residualTrace sigma r
  scalar_composition_is_noisy_or :
    ∀ sigma₂ sigma₁ : K,
      (scalarKeepLinearMap (K := K) (E := E) sigma₂).comp
          (scalarKeepLinearMap (K := K) (E := E) sigma₁) =
        scalarKeepLinearMap (K := K) (E := E) (satOrField sigma₁ sigma₂)

/-- THEOREM 12: the linear residual transport principle certificate. -/
theorem linearResidualTransportPrincipleCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    LinearResidualTransportPrincipleCertificate K E where
  operator_split_conserved := by
    intro keep r
    exact residual_eq_linearKeep_add_trace keep r
  residual_transport_law := by
    intro target keep x
    exact target_sub_linearResidualTransportUpdate target keep x
  trace_displacement_law := by
    intro target keep x
    exact linearResidualTransportDelta_eq_trace target keep x
  residual_law_unique := by
    intro target keep update h x
    exact update_eq_linearResidualTransportUpdate_of_residual_law target keep update h x
  trace_law_unique := by
    intro target keep update h x
    exact update_eq_linearResidualTransportUpdate_of_trace_law target keep update h x
  operator_composition := by
    intro target keep₂ keep₁ x
    exact linearResidualTransportUpdate_compose target keep₂ keep₁ x
  two_step_trace := by
    intro keep₂ keep₁ r
    exact linearResidualTrace_twoStep_eq_composite_trace keep₂ keep₁ r
  scalar_slice_is_relaxModule := by
    intro target sigma x
    exact scalar_linearResidualTransportUpdate_eq_relaxModule target sigma x
  scalar_trace_is_p743_trace := by
    intro sigma r
    exact scalar_linearResidualTrace_eq_residualTrace sigma r
  scalar_composition_is_noisy_or := by
    intro sigma₂ sigma₁
    exact scalarKeepLinearMap_comp (E := E) sigma₂ sigma₁

end AffineRelaxation
end SaturationMonoid
