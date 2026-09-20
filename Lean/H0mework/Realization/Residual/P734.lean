import H0mework.Realization.Relaxation.P733
import H0mework.Realization.Residual.Primitive

/-!
# Proposition 734: the residual transport principle

The affine update

`X ↦ X + sigma • (Target - X)`

is the scalar chart of a lower principle:

`residual ↦ keep residual`.

Given an arbitrary keep operator `K : E -> E`, the corresponding target-chart
state update is

`x ↦ target - K (target - x)`.

No linearity is required to state the residual law or the same-target
composition law.  Linearity, matrices, PDE semigroups, quantum unitary
operators, functors, and connections are stronger producer structures over the
same residual-transport shape.

The scalar keep operator `r ↦ (1 - sigma) • r` recovers `relaxModule`; at
target `1` on the scalar carrier it recovers `bumpSatField`.  Thus `bumpSat`
is not the first formula.  It is the target-one affine display of residual
transport.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

variable {K : Type u} [Field K]
variable {E : Type v} [AddCommGroup E] [Module K E]

-- `residualTransportUpdate` is defined by
-- `ResidualTransportPrimitiveKernel`; this proposition retains its richer
-- composition and scalar-chart consequences.

/-- The residual after a residual-transport update is exactly the transported
residual.  This is the first formula in target coordinates. -/
theorem residualTransportUpdate_residual
    (keep : E -> E) (target x : E) :
    target - residualTransportUpdate keep target x =
      keep (target - x) := by
  unfold residualTransportUpdate
  abel

/-- Same-target residual-transport updates compose by composition of keep
operators. -/
theorem residualTransportUpdate_compose
    (keep₁ keep₂ : E -> E) (target x : E) :
    residualTransportUpdate keep₂ target
        (residualTransportUpdate keep₁ target x) =
      residualTransportUpdate (keep₂ ∘ keep₁) target x := by
  unfold residualTransportUpdate
  simp

/-- Same-target residual transport is associative because function composition
of keep operators is associative. -/
theorem residualTransportUpdate_compose_assoc
    (keep₁ keep₂ keep₃ : E -> E) (target x : E) :
    residualTransportUpdate keep₃ target
        (residualTransportUpdate keep₂ target
          (residualTransportUpdate keep₁ target x)) =
      residualTransportUpdate (keep₃ ∘ keep₂ ∘ keep₁) target x := by
  unfold residualTransportUpdate
  simp

/-- The identity keep operator gives no state change. -/
theorem residualTransportUpdate_id_keep
    (target x : E) :
    residualTransportUpdate (fun r : E => r) target x = x := by
  unfold residualTransportUpdate
  simp

/-- The zero keep operator collapses immediately to the target. -/
theorem residualTransportUpdate_zero_keep
    (target x : E) :
    residualTransportUpdate (fun _ : E => 0) target x = target := by
  unfold residualTransportUpdate
  simp

/-- The scalar keep operator used by ordinary saturation and relaxation. -/
def scalarKeep (sigma : K) : E -> E :=
  fun r : E => (1 - sigma) • r

/-- Scalar keep residual transport is exactly `relaxModule`. -/
theorem residualTransportUpdate_scalarKeep_eq_relaxModule
    (target x : E) (sigma : K) :
    residualTransportUpdate (scalarKeep (E := E) sigma) target x =
      relaxModule target sigma x := by
  unfold residualTransportUpdate scalarKeep relaxModule
  module

/-- The scalar keep residual law specializes to the standard relaxation
residual law. -/
theorem residualTransportUpdate_scalarKeep_residual
    (target x : E) (sigma : K) :
    target - residualTransportUpdate (scalarKeep (E := E) sigma) target x =
      (1 - sigma) • (target - x) := by
  rw [residualTransportUpdate_scalarKeep_eq_relaxModule]
  exact target_sub_relaxModule target sigma x

/-- Composing scalar keep operators yields the noisy-OR scalar rate law. -/
theorem scalarKeep_compose_eq_satOr
    (sigma₁ sigma₂ : K) :
    scalarKeep (E := E) sigma₂ ∘ scalarKeep (E := E) sigma₁ =
      scalarKeep (E := E) (satOrField sigma₁ sigma₂) := by
  funext r
  unfold scalarKeep satOrField
  change (1 - sigma₂) • ((1 - sigma₁) • r) =
    (1 - (1 - (1 - sigma₁) * (1 - sigma₂))) • r
  rw [smul_smul]
  congr 1
  ring

/-- Therefore same-target scalar residual transport composes by noisy-OR. -/
theorem residualTransportUpdate_scalarKeep_compose_noisyOr
    (target x : E) (sigma₁ sigma₂ : K) :
    residualTransportUpdate (scalarKeep (E := E) sigma₂) target
        (residualTransportUpdate (scalarKeep (E := E) sigma₁) target x) =
      residualTransportUpdate
        (scalarKeep (E := E) (satOrField sigma₁ sigma₂)) target x := by
  rw [residualTransportUpdate_compose]
  rw [scalarKeep_compose_eq_satOr]

/-- On the scalar carrier and target `1`, scalar residual transport is exactly
`bumpSatField`. -/
theorem residualTransportUpdate_scalarKeep_targetOne_eq_bumpSat
    (h sigma : K) :
    residualTransportUpdate
        (scalarKeep (K := K) (E := K) sigma) 1 h =
      bumpSatField h sigma := by
  rw [residualTransportUpdate_scalarKeep_eq_relaxModule]
  unfold relaxModule bumpSatField
  ring

/-- P734 certificate: the residual transport principle and its scalar affine
display. -/
structure ResidualTransportPrincipleCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  residual_transport_law :
    ∀ keep : E -> E, ∀ target x : E,
      target - residualTransportUpdate keep target x = keep (target - x)
  keep_composition_law :
    ∀ keep₁ keep₂ : E -> E, ∀ target x : E,
      residualTransportUpdate keep₂ target
          (residualTransportUpdate keep₁ target x) =
        residualTransportUpdate (keep₂ ∘ keep₁) target x
  id_keep_noop :
    ∀ target x : E,
      residualTransportUpdate (fun r : E => r) target x = x
  zero_keep_hits_target :
    ∀ target x : E,
      residualTransportUpdate (fun _ : E => 0) target x = target
  scalar_keep_is_relaxModule :
    ∀ target x : E, ∀ sigma : K,
      residualTransportUpdate (scalarKeep (K := K) (E := E) sigma) target x =
        relaxModule target sigma x
  scalar_keep_composes_by_noisyOr :
    ∀ sigma₁ sigma₂ : K,
      scalarKeep (K := K) (E := E) sigma₂ ∘
          scalarKeep (K := K) (E := E) sigma₁ =
        scalarKeep (K := K) (E := E) (satOrField sigma₁ sigma₂)
  target_one_scalar_keep_is_bumpSat :
    ∀ h sigma : K,
      residualTransportUpdate
          (scalarKeep (K := K) (E := K) sigma) 1 h =
        bumpSatField h sigma

/-- THEOREM 1: every module carrier supports the residual transport principle,
and scalar keep recovers the affine relaxation / bumpSat display. -/
theorem residualTransportPrincipleCertificate :
    ResidualTransportPrincipleCertificate K E where
  residual_transport_law :=
    residualTransportUpdate_residual
  keep_composition_law :=
    residualTransportUpdate_compose
  id_keep_noop :=
    residualTransportUpdate_id_keep
  zero_keep_hits_target :=
    residualTransportUpdate_zero_keep
  scalar_keep_is_relaxModule :=
    residualTransportUpdate_scalarKeep_eq_relaxModule
  scalar_keep_composes_by_noisyOr :=
    scalarKeep_compose_eq_satOr
  target_one_scalar_keep_is_bumpSat :=
    residualTransportUpdate_scalarKeep_targetOne_eq_bumpSat

end AffineRelaxation
end SaturationMonoid
