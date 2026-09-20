/-
  Proposition 452: the one-loop coefficient as a finite carrier trace.

  P451 proves that once a carrier supplies a linear self-rate

      eta(sigma) = b0 * sigma,

  residual/complement saturation forces the one-loop quadratic step

      sigma' - sigma = -b0 * sigma^2.

  This file opens the coefficient one level: for a finite carrier, `b0` is not
  an opaque scalar but the sum of signed channel contributions.  The physical
  SU(7)/Standard-Model calculation still has to supply the concrete channel
  type and contribution weights; once it does, the beta functional form is
  inherited from P451.
-/

import H0mework.Physics.RepresentationSources.P451

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

open scoped BigOperators

noncomputable section

/-- A finite carrier for the one-loop coefficient.  The entries may be signed:
gauge/self-interaction and matter/screening contributions are represented by
the same additive trace surface. -/
structure FiniteOneLoopCarrier (Channel : Type*) [Fintype Channel] where
  contribution : Channel -> ℝ

namespace FiniteOneLoopCarrier

variable {Channel : Type*} [Fintype Channel]

/-- The beta coefficient is the finite trace/sum of carrier contributions. -/
def b0 (C : FiniteOneLoopCarrier Channel) : ℝ :=
  ∑ c : Channel, C.contribution c

/-- Forget the finite trace presentation to P451's scalar carrier. -/
def toOneLoopCarrier (C : FiniteOneLoopCarrier Channel) : OneLoopCarrier where
  b0 := C.b0

/-- The self-rate is the finite carrier trace times the running sigma. -/
def linearSelfRate (C : FiniteOneLoopCarrier Channel) (σ : ℝ) : ℝ :=
  C.b0 * σ

/-- The residual/complement step induced by the finite carrier. -/
def residualSelfBumpStep (C : FiniteOneLoopCarrier Channel) (σ : ℝ) : ℝ :=
  residualBumpStep σ (C.linearSelfRate σ)

/-- Opening the scalar `b0` shows the coefficient is exactly the channel sum. -/
theorem b0_eq_sum (C : FiniteOneLoopCarrier Channel) :
    C.b0 = ∑ c : Channel, C.contribution c := by
  rfl

/-- Closed form with the finite trace coefficient. -/
theorem residualSelfBumpStep_eq (C : FiniteOneLoopCarrier Channel) (σ : ℝ) :
    C.residualSelfBumpStep σ =
      σ - (∑ c : Channel, C.contribution c) * σ ^ 2 := by
  rw [residualSelfBumpStep, residualBumpStep, linearSelfRate, b0, bumpSatField_eq]
  ring

/-- The finite carrier trace gives the one-loop beta increment. -/
theorem residualSelfBumpStep_delta_eq_oneLoop
    (C : FiniteOneLoopCarrier Channel) (σ : ℝ) :
    C.residualSelfBumpStep σ - σ =
      -(∑ c : Channel, C.contribution c) * σ ^ 2 := by
  rw [residualSelfBumpStep_eq]
  ring

/-- The finite carrier presentation is definitionally compatible with the
scalar-carrier theorem from P451. -/
theorem residualSelfBumpStep_eq_scalarCarrier
    (C : FiniteOneLoopCarrier Channel) (σ : ℝ) :
    C.residualSelfBumpStep σ =
      C.toOneLoopCarrier.residualSelfBumpStep σ := by
  rfl

end FiniteOneLoopCarrier

end

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
