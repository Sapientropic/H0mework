/-
  Proposition 454: feed the Standard-Model one-loop carrier back into the
  residual saturation beta step.

  P451 proves the residual self-bump law for any scalar coefficient.
  P453 computes the Standard-Model coefficient table in the asymptotic
  convention.  This file composes those two facts: each Standard-Model gauge
  factor gets a concrete running-sigma step law.
-/

import H0mework.Physics.RepresentationSources.P453

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

noncomputable section

/-- The P451 scalar one-loop carrier selected by a Standard-Model gauge
factor.  The coefficient is the P453 asymptotic `b0`, cast to `ℝ`. -/
def standardModelOneLoopCarrier (G : StandardModelGaugeFactor) :
    OneLoopCarrier where
  b0 := (standardModelAsymptoticB0 G : ℝ)

/-- General Standard-Model residual beta step:
`sigma' - sigma = -b_asym(G) * sigma^2`. -/
theorem standardModelResidualSelfBump_delta
    (G : StandardModelGaugeFactor) (σ : ℝ) :
    (standardModelOneLoopCarrier G).residualSelfBumpStep σ - σ =
      -(standardModelAsymptoticB0 G : ℝ) * σ ^ 2 := by
  exact OneLoopCarrier.residualSelfBumpStep_delta_eq_oneLoop
    (standardModelOneLoopCarrier G) σ

/-- Color/QCD running-sigma step: `delta sigma = -7 sigma^2`. -/
theorem standardModelResidualSelfBump_delta_color (σ : ℝ) :
    (standardModelOneLoopCarrier .colorSU3).residualSelfBumpStep σ - σ =
      -(7 : ℝ) * σ ^ 2 := by
  rw [standardModelResidualSelfBump_delta,
    standardModelAsymptoticB0, qcdSixFlavor_asymptoticB0]
  norm_num

/-- Weak `SU(2)` running-sigma step:
`delta sigma = -(19/6) sigma^2`. -/
theorem standardModelResidualSelfBump_delta_weak (σ : ℝ) :
    (standardModelOneLoopCarrier .weakSU2).residualSelfBumpStep σ - σ =
      -((19 : ℝ) / 6) * σ ^ 2 := by
  rw [standardModelResidualSelfBump_delta,
    standardModelAsymptoticB0, weakStandardModel_asymptoticB0]
  norm_num

/-- Hypercharge running-sigma step:
`b_asym = -41/6`, hence `delta sigma = +(41/6) sigma^2`. -/
theorem standardModelResidualSelfBump_delta_hypercharge (σ : ℝ) :
    (standardModelOneLoopCarrier .hyperchargeU1).residualSelfBumpStep σ - σ =
      ((41 : ℝ) / 6) * σ ^ 2 := by
  rw [standardModelResidualSelfBump_delta,
    standardModelAsymptoticB0, hyperchargeStandardModel_asymptoticB0]
  ring

end

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
