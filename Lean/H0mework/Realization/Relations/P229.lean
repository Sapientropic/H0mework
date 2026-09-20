import H0mework.Realization.Relations.P223

/-!
# Proposition 229: gamma-density expectation producer for the P170 bridge

P170/P219/P220 already close the certificate plumbing:

* P170 transports finite-mixture-to-gamma convergence to shifted-power.
* P219 names the canonical bridge certificate.
* P220/P221 produce finite-grid / countable-schedule certificates from the
  strong law, provided the Laplace test expectation is the normalized gamma
  Laplace target.

This file discharges the density-level mathematical content of that expectation
field.  It proves directly that integrating the Laplace kernel against the
gamma density gives P147's normalized gamma Laplace functional, hence the
shifted-power target.

Boundary: this is not yet the full `HasLaw sampleRate (gammaMeasure ...)`
adapter for P220.  It proves the density/Laplace identity that such an adapter
must use; the random-variable-law bridge remains a separate mechanism theorem.
-/

open Set
open scoped Real Topology

noncomputable section

namespace GammaMixtureForgetting

/-! ## Gamma-density Laplace expectation -/

/-- The normalized gamma-density Laplace expectation, written as a positive
half-line integral.

This is the density-level version of the expectation field consumed by the
strong-law bridge: gamma density times the Laplace test kernel
`exp (-(time * x))`. -/
def normalizedGammaDensityLaplace (shape rate time : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ),
    gammaLaplaceNormalizer shape rate *
      (x ^ (shape - 1) * Real.exp (-(rate * x)) *
        Real.exp (-(time * x)))

/-- THEOREM 1: the normalized gamma-density Laplace expectation is exactly
P147's normalized gamma Laplace functional.

This is the core producer-side identity missing from the P170 certificate
story: the `hexpect` target in the strong-law bridge is not arbitrary; it is
the Laplace transform of the gamma density. -/
theorem normalizedGammaDensityLaplace_eq_normalizedGammaLaplace
    (shape rate time : ℝ) :
    normalizedGammaDensityLaplace shape rate time =
      normalizedGammaLaplace shape rate time := by
  rw [normalizedGammaDensityLaplace, normalizedGammaLaplace,
    unnormalizedGammaLaplace]
  rw [MeasureTheory.integral_const_mul]
  apply congrArg (fun z => gammaLaplaceNormalizer shape rate * z)
  apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
  filter_upwards [] with x hx
  have harg : -(rate * x) + -(time * x) = -(rate + time) * x := by
    ring
  calc
    x ^ (shape - 1) * Real.exp (-(rate * x)) * Real.exp (-(time * x))
        = x ^ (shape - 1) *
            (Real.exp (-(rate * x)) * Real.exp (-(time * x))) := by
          ring
    _ = x ^ (shape - 1) *
          Real.exp (-(rate * x) + -(time * x)) := by
          rw [Real.exp_add]
    _ = x ^ (shape - 1) * Real.exp (-(rate + time) * x) := by
          rw [harg]

/-- THEOREM 2: under positive gamma parameters and nonnegative time, the
gamma-density Laplace expectation is the shifted-power retention curve. -/
theorem normalizedGammaDensityLaplace_eq_shiftedPower
    {shape rate time : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htime : 0 ≤ time) :
    normalizedGammaDensityLaplace shape rate time =
      (1 + time / rate) ^ (-shape) := by
  rw [normalizedGammaDensityLaplace_eq_normalizedGammaLaplace]
  exact normalizedGammaLaplace_eq_shifted_power hshape hrate htime

/-!
  Summary:
  - P229 proves the density-level expectation target consumed by P220.
  - The finite-mixture bridge is now layered:
    P170 transport, P219 canonical certificate, P220/P221 strong-law producer,
    P222/P223 schedule-to-all-time continuity, and P229 gamma-density
    expectation.

  Remaining boundary:
  - Turn `sampleRate` having gamma law into the P220 expectation field.
  - Deterministic quadrature / order-statistics / runtime mechanism
    faithfulness remain separate producers.
-/


end GammaMixtureForgetting
