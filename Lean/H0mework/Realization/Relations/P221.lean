import H0mework.Realization.Relations.P220

/-!
# Proposition 221: countable-schedule strong-law bridge

P220 proves the LLN-to-P219 bridge for finite observation grids.  The same
argument works for any countable observation schedule: Mathlib's `ae_all_iff`
allows us to intersect countably many almost-sure convergence events.

This is the largest almost-sure time surface available without extra analytic
structure.  It still does not prove simultaneous convergence for all real
times; that would need a separate continuity/equicontinuity or process-level
certificate.
-/

namespace FiniteGammaBridgeCertificate

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ProbabilityTheory

noncomputable section

/-! ## Countable observation schedules -/

/-- A countable family of nonnegative observation times. -/
structure CountableObservationSchedule where
  Time : Type*
  inst : Countable Time
  time : Time → ℝ
  nonneg : ∀ τ : Time, 0 ≤ time τ

attribute [instance] CountableObservationSchedule.inst

/-- Every finite observation grid is a countable observation schedule. -/
def CountableObservationSchedule.ofFiniteGrid
    (grid : FiniteObservationGrid) :
    CountableObservationSchedule where
  Time := grid.Time
  inst := by infer_instance
  time := grid.time
  nonneg := grid.nonneg

/-! ## Canonical countable-schedule bridge certificate -/

/-- Canonical countable-schedule P170 bridge certificate.

Unlike P219's finite-grid facade, this supports any countable observation
schedule.  It is still a pointwise schedule certificate, not an all-real-time
certificate.
-/
structure CanonicalCountableScheduleGammaBridgeCertificate
    (schedule : CountableObservationSchedule) where
  mixture : ℕ → schedule.Time → ℝ
  shape : ℝ
  gammaRate : ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  tendsToGamma :
    ∀ τ : schedule.Time,
      Tendsto
        (fun N : ℕ => mixture N τ)
        atTop
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (schedule.time τ)))

/-- THEOREM 1: a countable-schedule bridge transports each scheduled time to
the shifted-power target. -/
theorem canonicalCountableScheduleGammaBridge_tendsto_shiftedPower
    {schedule : CountableObservationSchedule}
    (cert : CanonicalCountableScheduleGammaBridgeCertificate schedule)
    (τ : schedule.Time) :
    Tendsto
      (fun N : ℕ => cert.mixture N τ)
      atTop
      (𝓝 ((1 + schedule.time τ / cert.gammaRate) ^ (-cert.shape))) := by
  simpa [GammaMixtureForgetting.normalizedGammaLaplace_eq_shifted_power
      cert.shape_pos cert.gammaRate_pos (schedule.nonneg τ)]
    using cert.tendsToGamma τ

/-! ## Strong-law bridge to countable-schedule convergence -/

/-- THEOREM 2: on a countable observation schedule, iid/pairwise-independent
Laplace tests whose expectation is the normalized gamma Laplace target produce
almost sure pointwise convergence to the gamma target at every scheduled time.

This is the honest extension of P220: countable schedules are supported by
`ae_all_iff`; all-real-time convergence remains outside this theorem.
-/
theorem countableSchedule_laplace_empirical_tendsto_gamma_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {schedule : CountableObservationSchedule}
    (sampleRate : ℕ → Ω → ℝ)
    {shape gammaRate : ℝ}
    (_hshape : 0 < shape) (_hrate : 0 < gammaRate)
    (hint : ∀ τ : schedule.Time,
      Integrable (laplaceTest sampleRate (schedule.time τ) 0) μ)
    (hindep : ∀ τ : schedule.Time,
      Pairwise (fun i j : ℕ =>
        laplaceTest sampleRate (schedule.time τ) i ⟂ᵢ[μ]
          laplaceTest sampleRate (schedule.time τ) j))
    (hident : ∀ τ : schedule.Time, ∀ i : ℕ,
      IdentDistrib
        (laplaceTest sampleRate (schedule.time τ) i)
        (laplaceTest sampleRate (schedule.time τ) 0) μ μ)
    (hexpect : ∀ τ : schedule.Time,
      μ[laplaceTest sampleRate (schedule.time τ) 0] =
        GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (schedule.time τ)) :
    ∀ᵐ ω ∂μ, ∀ τ : schedule.Time,
      Tendsto
        (fun N : ℕ =>
          empiricalAverage
            (fun i : ℕ => laplaceTest sampleRate (schedule.time τ) i) N ω)
        atTop
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (schedule.time τ))) := by
  classical
  have hpoint : ∀ τ : schedule.Time, ∀ᵐ ω ∂μ,
      Tendsto
        (fun N : ℕ =>
          empiricalAverage
            (fun i : ℕ => laplaceTest sampleRate (schedule.time τ) i) N ω)
        atTop
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (schedule.time τ))) := by
    intro τ
    have hslln :=
      ProbabilityTheory.strong_law_ae_real
        (fun i : ℕ => laplaceTest sampleRate (schedule.time τ) i)
        (hint τ) (hindep τ) (hident τ)
    filter_upwards [hslln] with ω hω
    simpa [empiricalAverage, hexpect τ] using hω
  exact ae_all_iff.2 hpoint

/-- Compile one almost-sure sample path into the countable-schedule bridge
certificate. -/
def CanonicalCountableScheduleGammaBridgeCertificate.ofEmpiricalStrongLawPath
    {Ω : Type*} {schedule : CountableObservationSchedule}
    (sampleRate : ℕ → Ω → ℝ)
    {shape gammaRate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < gammaRate)
    (ω : Ω)
    (hconv : ∀ τ : schedule.Time,
      Tendsto
        (fun N : ℕ =>
          empiricalAverage
            (fun i : ℕ => laplaceTest sampleRate (schedule.time τ) i) N ω)
        atTop
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (schedule.time τ)))) :
    CanonicalCountableScheduleGammaBridgeCertificate schedule where
  mixture := fun N τ =>
    empiricalAverage
      (fun i : ℕ => laplaceTest sampleRate (schedule.time τ) i) N ω
  shape := shape
  gammaRate := gammaRate
  shape_pos := hshape
  gammaRate_pos := hrate
  tendsToGamma := hconv

/-- THEOREM 3: almost every sample path yields a canonical countable-schedule
bridge certificate with exactly the empirical Laplace averages as its mixture. -/
theorem countableSchedule_laplace_empirical_canonicalBridge_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {schedule : CountableObservationSchedule}
    (sampleRate : ℕ → Ω → ℝ)
    {shape gammaRate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < gammaRate)
    (hint : ∀ τ : schedule.Time,
      Integrable (laplaceTest sampleRate (schedule.time τ) 0) μ)
    (hindep : ∀ τ : schedule.Time,
      Pairwise (fun i j : ℕ =>
        laplaceTest sampleRate (schedule.time τ) i ⟂ᵢ[μ]
          laplaceTest sampleRate (schedule.time τ) j))
    (hident : ∀ τ : schedule.Time, ∀ i : ℕ,
      IdentDistrib
        (laplaceTest sampleRate (schedule.time τ) i)
        (laplaceTest sampleRate (schedule.time τ) 0) μ μ)
    (hexpect : ∀ τ : schedule.Time,
      μ[laplaceTest sampleRate (schedule.time τ) 0] =
        GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (schedule.time τ)) :
    ∀ᵐ ω ∂μ,
      ∃ cert : CanonicalCountableScheduleGammaBridgeCertificate schedule,
        ∀ (N : ℕ) (τ : schedule.Time),
          cert.mixture N τ =
            empiricalAverage
              (fun i : ℕ => laplaceTest sampleRate (schedule.time τ) i) N ω := by
  filter_upwards [
      countableSchedule_laplace_empirical_tendsto_gamma_ae
        sampleRate hshape hrate hint hindep hident hexpect] with ω hω
  refine ⟨
    CanonicalCountableScheduleGammaBridgeCertificate.ofEmpiricalStrongLawPath
      sampleRate hshape hrate ω hω, ?_⟩
  intro N τ
  rfl

/-- THEOREM 4: the strong-law countable-schedule bridge transports almost
surely to shifted-power convergence at every scheduled time. -/
theorem countableSchedule_laplace_empirical_tendsto_shiftedPower_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {schedule : CountableObservationSchedule}
    (sampleRate : ℕ → Ω → ℝ)
    {shape gammaRate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < gammaRate)
    (hint : ∀ τ : schedule.Time,
      Integrable (laplaceTest sampleRate (schedule.time τ) 0) μ)
    (hindep : ∀ τ : schedule.Time,
      Pairwise (fun i j : ℕ =>
        laplaceTest sampleRate (schedule.time τ) i ⟂ᵢ[μ]
          laplaceTest sampleRate (schedule.time τ) j))
    (hident : ∀ τ : schedule.Time, ∀ i : ℕ,
      IdentDistrib
        (laplaceTest sampleRate (schedule.time τ) i)
        (laplaceTest sampleRate (schedule.time τ) 0) μ μ)
    (hexpect : ∀ τ : schedule.Time,
      μ[laplaceTest sampleRate (schedule.time τ) 0] =
        GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (schedule.time τ)) :
    ∀ᵐ ω ∂μ, ∀ τ : schedule.Time,
      Tendsto
        (fun N : ℕ =>
          empiricalAverage
            (fun i : ℕ => laplaceTest sampleRate (schedule.time τ) i) N ω)
        atTop
        (𝓝 ((1 + schedule.time τ / gammaRate) ^ (-shape))) := by
  filter_upwards [
      countableSchedule_laplace_empirical_tendsto_gamma_ae
        sampleRate hshape hrate hint hindep hident hexpect] with ω hω τ
  exact canonicalCountableScheduleGammaBridge_tendsto_shiftedPower
    (CanonicalCountableScheduleGammaBridgeCertificate.ofEmpiricalStrongLawPath
      sampleRate hshape hrate ω hω) τ

/-!
  Summary:
  - P221 extends P220 from finite grids to arbitrary countable observation
    schedules.
  - This is the maximal almost-sure schedule bridge available from pointwise
    SLLN plus countable intersection alone.

  Still outside this theorem:
  - simultaneous convergence for all real times;
  - continuity/equicontinuity extension from a dense schedule;
  - a formal gamma sampler expectation theorem;
  - order-statistics, deterministic quadrature, parameter estimation, or
    runtime mechanism-faithfulness.
-/


end

end FiniteGammaBridgeCertificate
