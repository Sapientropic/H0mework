/-
  Proposition 451: residual self-bump gives the one-loop quadratic beta shape.

  The dangerous loose slogan is "self-bump sigma gives beta proportional to
  sigma squared".  In the raw saturation coordinate this is false:

      bumpSatField σ σ - σ = σ * (1 - σ).

  The one-loop quadratic shape appears in the residual/complement coordinate.
  If the carrier supplies a linear self-feedback rate `η = b₀ * σ` and that
  rate bumps the complement `1 - σ`, then the induced change of `σ` is exactly

      σ' - σ = - b₀ * σ^2.

  Thus the functional one-loop beta form is internal to the saturation law;
  only the coefficient `b₀` remains carrier/representation data.
-/

import H0mework.Physics.SourceContracts.P450

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

noncomputable section

/-! ## Raw self-bump is logistic, not one-loop -/

/-- Directly bumping `σ` by `σ` in the saturation coordinate. -/
def directSelfBump (σ : ℝ) : ℝ :=
  bumpSatField σ σ

/-- The direct self-bump increment. -/
def directSelfBumpDelta (σ : ℝ) : ℝ :=
  directSelfBump σ - σ

/-- Direct saturation self-bump has the logistic increment `σ * (1 - σ)`.
This theorem is the coordinate warning: the one-loop quadratic form does not
come from bumping the raw `σ` coordinate toward the ceiling. -/
theorem directSelfBumpDelta_eq_logistic (σ : ℝ) :
    directSelfBumpDelta σ = σ * (1 - σ) := by
  rw [directSelfBumpDelta, directSelfBump, bumpSatField_eq]
  ring

/-! ## Residual self-bump gives the quadratic beta form -/

/-- Bump the complement/residual coordinate `1 - σ` by rate `η`, then return to
the `σ` coordinate. -/
def residualBumpStep (σ η : ℝ) : ℝ :=
  1 - bumpSatField (1 - σ) η

/-- In the `σ` coordinate, bumping the complement by rate `η` changes `σ` by
`-η * σ`. -/
theorem residualBumpStep_delta_eq (σ η : ℝ) :
    residualBumpStep σ η - σ = -η * σ := by
  rw [residualBumpStep, bumpSatField_eq]
  ring

/-- A carrier contributes the one remaining datum for the one-loop shape: the
coefficient multiplying the self-rate.  This file does not compute `b₀`; it
proves that once the carrier supplies it, saturation forces the quadratic
functional form. -/
structure OneLoopCarrier where
  b0 : ℝ

namespace OneLoopCarrier

/-- The carrier-linear self-feedback rate `η(σ) = b₀ * σ`. -/
def linearSelfRate (C : OneLoopCarrier) (σ : ℝ) : ℝ :=
  C.b0 * σ

/-- The induced residual/complement step on the running `σ` coordinate. -/
def residualSelfBumpStep (C : OneLoopCarrier) (σ : ℝ) : ℝ :=
  residualBumpStep σ (C.linearSelfRate σ)

/-- Closed form of the residual self-bump step: `σ' = σ - b₀ σ²`. -/
theorem residualSelfBumpStep_eq (C : OneLoopCarrier) (σ : ℝ) :
    C.residualSelfBumpStep σ = σ - C.b0 * σ ^ 2 := by
  rw [residualSelfBumpStep, residualBumpStep, linearSelfRate, bumpSatField_eq]
  ring

/-- The discrete beta increment has one-loop quadratic form.  Scale orientation
chooses the physical sign; this residual orientation is the asymptotically-free
`-b₀ σ²` direction. -/
theorem residualSelfBumpStep_delta_eq_oneLoop (C : OneLoopCarrier) (σ : ℝ) :
    C.residualSelfBumpStep σ - σ = -C.b0 * σ ^ 2 := by
  rw [residualSelfBumpStep_eq]
  ring

/-- Equivalently, the magnitude of the residual self-bump increment is
`b₀ σ²`. -/
theorem residualSelfBumpStep_negative_delta_eq (C : OneLoopCarrier) (σ : ℝ) :
    -(C.residualSelfBumpStep σ - σ) = C.b0 * σ ^ 2 := by
  rw [residualSelfBumpStep_delta_eq_oneLoop]
  ring

end OneLoopCarrier

end

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
