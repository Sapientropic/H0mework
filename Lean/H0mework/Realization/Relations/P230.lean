import H0mework.Realization.Relations.P229
import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Proposition 230: gamma-law expectation adapter for the P170 bridge

P229 proved the density-level identity:

`∫₀∞ normalizer * x^(shape-1) * exp (-(rate*x)) * exp (-(time*x))
  = normalizedGammaLaplace shape rate time`.

This file connects that density identity to Mathlib's actual
`ProbabilityTheory.gammaMeasure`.  It then gives the reusable external
certificate shape consumed by P220: if a sampled rate has gamma law, its
Laplace test expectation is the normalized gamma Laplace target, hence the
shifted-power target.

This closes the `HasLaw` / `withDensity` adapter layer.  It still does not
prove that any concrete runtime sampler, quadrature routine, or empirical data
stream has gamma law; those are separate producer certificates.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Real Topology ENNReal

noncomputable section

namespace GammaMixtureForgetting

/-! ## Gamma measure to gamma-density Laplace expectation -/

private lemma ae_ne_zero_volume :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ (0 : ℝ) := by
  rw [MeasureTheory.ae_iff]
  simp [MeasureTheory.NullSingletonClass.measure_singleton
    (μ := (volume : Measure ℝ)) (0 : ℝ)]

private lemma gammaPDFReal_laplace_ae_eq_densityIndicator
    (shape rate time : ℝ) :
    (fun x : ℝ =>
        ProbabilityTheory.gammaPDFReal shape rate x * Real.exp (-(x * time)))
      =ᵐ[(volume : Measure ℝ)]
    fun x : ℝ =>
      (Ioi (0 : ℝ)).indicator
        (fun y : ℝ =>
          gammaLaplaceNormalizer shape rate *
            (y ^ (shape - 1) * Real.exp (-(rate * y)) *
              Real.exp (-(time * y)))) x := by
  filter_upwards [ae_ne_zero_volume] with x hx0
  by_cases hxpos : 0 < x
  · have hxnonneg : 0 ≤ x := hxpos.le
    rw [ProbabilityTheory.gammaPDFReal]
    simp [hxnonneg, hxpos, gammaLaplaceNormalizer, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm]
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
    have hxnotmem : x ∉ Ioi (0 : ℝ) := by
      simpa [mem_Ioi] using not_lt.mpr hxneg.le
    rw [ProbabilityTheory.gammaPDFReal]
    simp [not_le.mpr hxneg, hxnotmem]

/-- THEOREM 1: integrating the Laplace kernel against Mathlib's
`gammaMeasure` is exactly the P229 normalized gamma-density Laplace
expectation. -/
theorem gammaMeasure_laplaceExpectation_eq_normalizedGammaDensityLaplace
    {shape rate time : ℝ} (hshape : 0 < shape) (hrate : 0 < rate) :
    ∫ x, Real.exp (-(x * time)) ∂(ProbabilityTheory.gammaMeasure shape rate) =
      normalizedGammaDensityLaplace shape rate time := by
  rw [ProbabilityTheory.gammaMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · calc
      ∫ x,
          (ProbabilityTheory.gammaPDF shape rate x).toReal •
            Real.exp (-(x * time)) ∂(volume : Measure ℝ)
          = ∫ x,
              ProbabilityTheory.gammaPDFReal shape rate x *
                Real.exp (-(x * time)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            unfold ProbabilityTheory.gammaPDF
            rw [ENNReal.toReal_ofReal
              (ProbabilityTheory.gammaPDFReal_nonneg hshape hrate x)]
            simp [smul_eq_mul]
      _ = ∫ x,
            (Ioi (0 : ℝ)).indicator
              (fun y : ℝ =>
                gammaLaplaceNormalizer shape rate *
                  (y ^ (shape - 1) * Real.exp (-(rate * y)) *
                    Real.exp (-(time * y)))) x := by
            exact integral_congr_ae
              (gammaPDFReal_laplace_ae_eq_densityIndicator shape rate time)
      _ = normalizedGammaDensityLaplace shape rate time := by
            rw [MeasureTheory.integral_indicator measurableSet_Ioi]
            rfl
  · unfold ProbabilityTheory.gammaPDF
    exact (ProbabilityTheory.measurable_gammaPDFReal shape rate).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x => by
      unfold ProbabilityTheory.gammaPDF
      exact ENNReal.ofReal_lt_top

/-- THEOREM 2: the gamma-measure Laplace expectation is P147's normalized
gamma Laplace target. -/
theorem gammaMeasure_laplaceExpectation_eq_normalizedGammaLaplace
    {shape rate time : ℝ} (hshape : 0 < shape) (hrate : 0 < rate) :
    ∫ x, Real.exp (-(x * time)) ∂(ProbabilityTheory.gammaMeasure shape rate) =
      normalizedGammaLaplace shape rate time := by
  rw [gammaMeasure_laplaceExpectation_eq_normalizedGammaDensityLaplace
    hshape hrate]
  exact normalizedGammaDensityLaplace_eq_normalizedGammaLaplace
    shape rate time

/-- THEOREM 3: under positive gamma parameters and nonnegative time, the
gamma-measure Laplace expectation is the shifted-power retention curve. -/
theorem gammaMeasure_laplaceExpectation_eq_shiftedPower
    {shape rate time : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htime : 0 ≤ time) :
    ∫ x, Real.exp (-(x * time)) ∂(ProbabilityTheory.gammaMeasure shape rate) =
      (1 + time / rate) ^ (-shape) := by
  rw [gammaMeasure_laplaceExpectation_eq_normalizedGammaLaplace
    hshape hrate]
  exact normalizedGammaLaplace_eq_shifted_power hshape hrate htime

/-! ## HasLaw adapter for strong-law producer expectations -/

/-- THEOREM 4: if a sampled rate has gamma law, then its Laplace test
expectation is exactly the normalized gamma Laplace target consumed by P220's
`hexpect` field. -/
theorem HasLaw.laplaceExpectation_eq_normalizedGammaLaplace
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {sampleRate : Ω → ℝ} {shape rate time : ℝ}
    (hlaw : HasLaw sampleRate
      (ProbabilityTheory.gammaMeasure shape rate) P)
    (hshape : 0 < shape) (hrate : 0 < rate) :
    P[fun ω => Real.exp (-(sampleRate ω * time))] =
      normalizedGammaLaplace shape rate time := by
  rw [← gammaMeasure_laplaceExpectation_eq_normalizedGammaLaplace
    hshape hrate]
  have hcont : Continuous (fun x : ℝ => Real.exp (-(x * time))) := by
    fun_prop
  exact hlaw.integral_comp hcont.aestronglyMeasurable

/-- THEOREM 5: the same `HasLaw` adapter, transported all the way to the
shifted-power curve. -/
theorem HasLaw.laplaceExpectation_eq_shiftedPower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {sampleRate : Ω → ℝ} {shape rate time : ℝ}
    (hlaw : HasLaw sampleRate
      (ProbabilityTheory.gammaMeasure shape rate) P)
    (hshape : 0 < shape) (hrate : 0 < rate) (htime : 0 ≤ time) :
    P[fun ω => Real.exp (-(sampleRate ω * time))] =
      (1 + time / rate) ^ (-shape) := by
  rw [HasLaw.laplaceExpectation_eq_normalizedGammaLaplace
    hlaw hshape hrate]
  exact normalizedGammaLaplace_eq_shifted_power hshape hrate htime

/-!
  Summary:
  - P230 upgrades P229 from density-level expectation to Mathlib
    `gammaMeasure` expectation.
  - It also gives the direct `HasLaw` adapter that P220 needs for its
    expectation identity field.

  Remaining boundary:
  - A concrete sampler/runtime must still prove or import `HasLaw sampleRate
    (gammaMeasure shape rate) P`.
  - Deterministic quadrature, order-statistics, parameter estimation, and
    runtime mechanism-faithfulness remain separate producer obligations.
-/


end GammaMixtureForgetting
