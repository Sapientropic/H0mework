/-
  Proposition 476: coordinate-linearized flow normal form.

  P475 puts the Yukawa sampled residual flow and one-loop gauge inverse-flow in
  one running-sigma receipt.  This file pushes the unification one layer lower:
  both are coordinate-linearized flows.

  * For fixed-target real relaxation, the linearizing coordinate is
        `x ↦ target - x`;
    the coordinate action is multiplication by the residual
        `exp(-lambda * t)`.

  * For one-loop gauge running, the linearizing coordinate is
        `sigma ↦ 1 / sigma`;
    the coordinate action is affine translation
        `c ↦ c + b0 * t`.

  The common statement is not that these two coordinates are identical.  It is
  that both satisfy the same time-action law in their own natural coordinate.

  Boundary: this does not choose physical clocks, beta coefficients, thresholds,
  or higher-loop corrections.  It proves the shared mathematical normal form of
  the currently certified flows.
-/

import H0mework.Physics.CouplingSources.P475

namespace SaturationMonoid

noncomputable section

/-! ## Abstract coordinate-action law -/

/-- A flow is coordinate-linearized when, on its declared valid patch, applying
the flow and then reading the coordinate equals acting on the coordinate.  The
coordinate action itself composes by time addition.

The action may be multiplicative, affine, unitary, etc.; the structure only
records the common time-action spine. -/
structure CoordinateActionLaw
    {X C : Type*}
    (flow : ℝ -> X -> X)
    (coord : X -> C)
    (action : ℝ -> C -> C)
    (valid : ℝ -> X -> Prop) : Prop where
  coord_flow :
    ∀ t x, valid t x -> coord (flow t x) = action t (coord x)
  action_zero :
    ∀ c, action 0 c = c
  action_add :
    ∀ t s c, action s (action t c) = action (t + s) c

namespace CoordinateActionLaw

/-- THEOREM 1: coordinate evolution over two times is computed by composing
the coordinate actions. -/
theorem coord_flow_two_step
    {X C : Type*}
    {flow : ℝ -> X -> X}
    {coord : X -> C}
    {action : ℝ -> C -> C}
    {valid : ℝ -> X -> Prop}
    (L : CoordinateActionLaw flow coord action valid)
    (t s : ℝ) (x : X)
    (ht : valid t x)
    (hs : valid s (flow t x)) :
    coord (flow s (flow t x)) =
      action (t + s) (coord x) := by
  rw [L.coord_flow s (flow t x) hs]
  rw [L.coord_flow t x ht]
  exact L.action_add t s (coord x)

end CoordinateActionLaw

namespace AffineRelaxation

/-! ## Fixed-target residual coordinate -/

/-- THEOREM 2: in the coordinate `target - x`, the real decay flow is residual
scaling. -/
theorem target_sub_realDecayRelaxFlow
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda t : ℝ) (x : E) :
    target - realDecayRelaxFlow target lambda t x =
      realDecayResidual lambda t • (target - x) := by
  rw [realDecayRelaxFlow_eq_closed]
  module

/-- THEOREM 3: residual scaling is a time-additive action. -/
theorem realDecayResidual_smul_action_add
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lambda t s : ℝ) (v : E) :
    realDecayResidual lambda s •
        (realDecayResidual lambda t • v) =
      realDecayResidual lambda (t + s) • v := by
  rw [smul_smul, realDecayResidual_add]
  congr 1
  ring

/-- THEOREM 4: fixed-target real relaxation is coordinate-linearized by the
residual coordinate `target - x`. -/
theorem realDecayCoordinateActionLaw
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda : ℝ) :
    CoordinateActionLaw
      (fun t x => realDecayRelaxFlow target lambda t x)
      (fun x => target - x)
      (fun t v => realDecayResidual lambda t • v)
      (fun _ _ => True) where
  coord_flow := by
    intro t x _
    exact target_sub_realDecayRelaxFlow target lambda t x
  action_zero := by
    intro v
    simp [realDecayResidual_zero]
  action_add := by
    intro t s v
    exact realDecayResidual_smul_action_add lambda t s v

end AffineRelaxation

namespace StandardModelConstraint
namespace RunningSigmaBeta

/-! ## One-loop inverse-coupling coordinate -/

/-- THEOREM 5: affine inverse-coupling translation is a time-additive action.
-/
theorem inverseCouplingAffineAction_add
    (b0 t s c : ℝ) :
    (c + b0 * t) + b0 * s =
      c + b0 * (t + s) := by
  ring

/-- THEOREM 6: one-loop sigma flow is coordinate-linearized by inverse
coupling `sigma ↦ 1/sigma` on the nonzero patch. -/
theorem oneLoopInverseCoordinateActionLaw
    (b0 : ℝ) :
    CoordinateActionLaw
      (fun t sigma => oneLoopSigmaFlow b0 sigma t)
      (fun sigma => (1 : ℝ) / sigma)
      (fun t c => c + b0 * t)
      (fun _ sigma => sigma ≠ 0) where
  coord_flow := by
    intro t sigma hsigma
    exact oneLoopSigmaFlow_inverse_linear b0 sigma t hsigma
  action_zero := by
    intro c
    ring
  action_add := by
    intro t s c
    exact inverseCouplingAffineAction_add b0 t s c

/-- THEOREM 7: every Standard-Model gauge factor inherits the inverse-coordinate
linearization with its carrier-selected one-loop slope. -/
theorem standardModelInverseCoordinateActionLaw
    (G : StandardModelGaugeFactor) :
    CoordinateActionLaw
      (fun t sigma => standardModelOneLoopSigmaFlow G sigma t)
      (fun sigma => (1 : ℝ) / sigma)
      (fun t c => c + (standardModelAsymptoticB0 G : ℝ) * t)
      (fun _ sigma => sigma ≠ 0) := by
  exact oneLoopInverseCoordinateActionLaw
    (standardModelAsymptoticB0 G : ℝ)

end RunningSigmaBeta
end StandardModelConstraint

/-! ## Bundled receipt -/

/-- A compact receipt that the two certified running-sigma flow families share
the same coordinate-action normal form. -/
structure CoordinateLinearizedRunningSigmaReceipt : Prop where
  real_decay_coordinate :
    ∀ {E : Type*} [AddCommGroup E] [Module ℝ E],
      ∀ target : E, ∀ lambda : ℝ,
        CoordinateActionLaw
          (fun t x =>
            AffineRelaxation.realDecayRelaxFlow target lambda t x)
          (fun x => target - x)
          (fun t v => AffineRelaxation.realDecayResidual lambda t • v)
          (fun _ _ => True)
  one_loop_inverse_coordinate :
    ∀ b0 : ℝ,
      CoordinateActionLaw
        (fun t sigma =>
          StandardModelConstraint.RunningSigmaBeta.oneLoopSigmaFlow
            b0 sigma t)
        (fun sigma => (1 : ℝ) / sigma)
        (fun t c => c + b0 * t)
        (fun _ sigma => sigma ≠ 0)
  standard_model_inverse_coordinate :
    ∀ G : StandardModelConstraint.RunningSigmaBeta.StandardModelGaugeFactor,
      CoordinateActionLaw
        (fun t sigma =>
          StandardModelConstraint.RunningSigmaBeta.standardModelOneLoopSigmaFlow
            G sigma t)
        (fun sigma => (1 : ℝ) / sigma)
        (fun t c =>
          c +
            (StandardModelConstraint.RunningSigmaBeta.standardModelAsymptoticB0
              G : ℝ) * t)
        (fun _ sigma => sigma ≠ 0)

/-- THEOREM 8: the coordinate-linearized running-sigma receipt. -/
theorem coordinateLinearizedRunningSigmaReceipt :
    CoordinateLinearizedRunningSigmaReceipt where
  real_decay_coordinate :=
    fun target lambda =>
      AffineRelaxation.realDecayCoordinateActionLaw target lambda
  one_loop_inverse_coordinate :=
    StandardModelConstraint.RunningSigmaBeta.oneLoopInverseCoordinateActionLaw
  standard_model_inverse_coordinate :=
    StandardModelConstraint.RunningSigmaBeta.standardModelInverseCoordinateActionLaw

end

end SaturationMonoid
