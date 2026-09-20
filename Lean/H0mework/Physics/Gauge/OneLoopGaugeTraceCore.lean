import Mathlib.Data.Rat.Defs

/-!
# Dependency-light one-loop gauge-trace coefficient

This leaf module contains only the universal trace-form bookkeeping consumed
by new representation-first physics work.  It deliberately uses a
physics-core namespace while the Proposition spine still owns its historical
compatibility structure; the downstream regression checks their numerical
agreement.  It imports no P459/P508/P523 carrier and selects no matter content,
coupling boundary, or empirical scale.
-/

namespace SaturationMonoid.PhysicsCore.OneLoopGaugeTraceCore

/-- Gauge theory one-loop input in trace form:
`Σ_Weyl T(R)` and `Σ_complexScalar T(R)` already include all representation
multiplicities. -/
structure GaugeTraceOneLoopInput where
  adjointCasimir : ℚ
  weylDynkinTrace : ℚ
  scalarDynkinTrace : ℚ

namespace GaugeTraceOneLoopInput

/-- `b_asym = (11/3)C_A - (2/3)Σ_Weyl T(R) -
(1/3)Σ_scalar T(R)`. -/
def asymptoticB0 (input : GaugeTraceOneLoopInput) : ℚ :=
  (11 / 3) * input.adjointCasimir -
    (2 / 3) * input.weylDynkinTrace -
    (1 / 3) * input.scalarDynkinTrace

def standardBetaCoefficient (input : GaugeTraceOneLoopInput) : ℚ :=
  -input.asymptoticB0

theorem standardBetaCoefficient_eq_neg_asymptoticB0
    (input : GaugeTraceOneLoopInput) :
    input.standardBetaCoefficient = -input.asymptoticB0 := rfl

end GaugeTraceOneLoopInput
end SaturationMonoid.PhysicsCore.OneLoopGaugeTraceCore
