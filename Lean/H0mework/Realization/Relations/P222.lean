import H0mework.Realization.Relations.P221

/-!
# Proposition 222: schedule-close certificates for the P170 bridge

P220/P221 produce convergence on finite or countable observation schedules.
P219's canonical P170 bridge, however, is an all-real-time certificate: it asks
for convergence at every nonnegative time.

This file names and proves the missing analytic adapter.  If a producer can
show that every nonnegative time is uniformly close to some scheduled time
both at the finite-mixture level and at the gamma target level, then countable
schedule convergence extends to all nonnegative real times.  No random
sampling theorem is smuggled in here: the extra continuity/equicontinuity
content is an explicit certificate field.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## Countable schedule to all-time convergence -/

/-- A countable-schedule-to-all-time close certificate.

For every nonnegative real time and every error budget `ε`, the certificate
finds a scheduled time `τ` such that:

* every finite mixture value at `time` is within `ε / 3` of its value at `τ`;
* the continuous target at `τ` is within `ε / 3` of the continuous target at
  `time`.

Together with convergence at `τ`, the triangle inequality gives convergence at
`time`.  This is the reusable "dense/equicontinuous schedule" obligation:
P221 supplies the scheduled convergence; this certificate supplies the
all-real-time extension.
-/
structure CountableScheduleCloseCertificate
    (schedule : CountableObservationSchedule)
    (mixture : ℕ → ℝ → ℝ) (target : ℝ → ℝ) where
  close :
    ∀ {time : ℝ}, 0 ≤ time → ∀ ε : ℝ, 0 < ε →
      ∃ τ : schedule.Time,
        (∀ N : ℕ,
          dist (mixture N time) (mixture N (schedule.time τ)) < ε / 3) ∧
        dist (target (schedule.time τ)) (target time) < ε / 3

/-- THEOREM 1: convergence on a countable schedule plus a close certificate
extends to convergence at every nonnegative real time. -/
theorem tendsto_allTime_of_countableSchedule_close
    {schedule : CountableObservationSchedule}
    {mixture : ℕ → ℝ → ℝ} {target : ℝ → ℝ}
    (hconv :
      ∀ τ : schedule.Time,
        Tendsto
          (fun N : ℕ => mixture N (schedule.time τ))
          atTop
          (𝓝 (target (schedule.time τ))))
    (closeCert : CountableScheduleCloseCertificate schedule mixture target)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto (fun N : ℕ => mixture N time) atTop (𝓝 (target time)) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  rcases closeCert.close htime ε hε with ⟨τ, hmix_close, htarget_close⟩
  have hthird : 0 < ε / 3 := by linarith
  rcases Metric.tendsto_atTop.1 (hconv τ) (ε / 3) hthird with
    ⟨N0, hN0⟩
  refine ⟨N0, ?_⟩
  intro N hN
  have hmid :
      dist (mixture N (schedule.time τ)) (target (schedule.time τ)) <
        ε / 3 := hN0 N hN
  have hsum :
      dist (mixture N time) (target time) <
        ε / 3 + (ε / 3 + ε / 3) := by
    calc
      dist (mixture N time) (target time)
          ≤ dist (mixture N time) (mixture N (schedule.time τ)) +
            dist (mixture N (schedule.time τ)) (target time) :=
              dist_triangle _ _ _
      _ ≤ dist (mixture N time) (mixture N (schedule.time τ)) +
            (dist (mixture N (schedule.time τ))
              (target (schedule.time τ)) +
             dist (target (schedule.time τ)) (target time)) := by
              have htri :
                  dist (mixture N (schedule.time τ)) (target time) ≤
                    dist (mixture N (schedule.time τ))
                      (target (schedule.time τ)) +
                    dist (target (schedule.time τ)) (target time) :=
                dist_triangle _ _ _
              nlinarith
      _ < ε / 3 + (ε / 3 + ε / 3) := by
              exact add_lt_add (hmix_close N)
                (add_lt_add hmid htarget_close)
  have hsum_eq : ε / 3 + (ε / 3 + ε / 3) = ε := by ring
  simpa [hsum_eq] using hsum

/-! ## Gamma-specific all-time bridge extension -/

/-- A gamma-specific all-time extension certificate.

This is the missing P170 producer bridge between P221 and P219: scheduled
convergence is paired with an explicit close certificate for the all-time
mixture and the normalized gamma target.
-/
structure CountableScheduleToAllTimeGammaBridgeCertificate
    (schedule : CountableObservationSchedule) where
  mixture : ℕ → ℝ → ℝ
  shape : ℝ
  gammaRate : ℝ
  shape_pos : 0 < shape
  gammaRate_pos : 0 < gammaRate
  schedule_tendsto_gamma :
    ∀ τ : schedule.Time,
      Tendsto
        (fun N : ℕ => mixture N (schedule.time τ))
        atTop
        (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
          shape gammaRate (schedule.time τ)))
  close_to_schedule :
    CountableScheduleCloseCertificate schedule mixture
      (GammaMixtureForgetting.normalizedGammaLaplace shape gammaRate)

/-- THEOREM 2: a countable-schedule gamma bridge plus a close certificate
compiles into the canonical all-time P170 bridge certificate. -/
def CountableScheduleToAllTimeGammaBridgeCertificate.toCanonicalFiniteGammaBridge
    {schedule : CountableObservationSchedule}
    (cert : CountableScheduleToAllTimeGammaBridgeCertificate schedule) :
    CanonicalFiniteGammaBridgeCertificate ℕ atTop where
  mixture := cert.mixture
  shape := cert.shape
  gammaRate := cert.gammaRate
  shape_pos := cert.shape_pos
  gammaRate_pos := cert.gammaRate_pos
  tendsToGamma := by
    intro time htime
    exact tendsto_allTime_of_countableSchedule_close
      cert.schedule_tendsto_gamma cert.close_to_schedule htime

/-- THEOREM 3: the gamma all-time extension certificate transports all the
way to shifted-power convergence. -/
theorem countableScheduleToAllTimeGammaBridge_tendsto_shiftedPower
    {schedule : CountableObservationSchedule}
    (cert : CountableScheduleToAllTimeGammaBridgeCertificate schedule)
    {time : ℝ} (htime : 0 ≤ time) :
    Tendsto
      (fun N : ℕ => cert.mixture N time)
      atTop
      (𝓝 ((1 + time / cert.gammaRate) ^ (-cert.shape))) :=
  canonicalFiniteGammaBridge_tendsto_shiftedPower
    cert.toCanonicalFiniteGammaBridge htime

/-!
  Summary:
  - P222 does not claim that countable SLLN convergence automatically implies
    all-real-time convergence.
  - It isolates the exact extra obligation: a schedule-close/equicontinuity
    certificate.
  - Once that certificate is supplied, the route
    `countable schedule convergence → P219 all-time bridge → shifted-power`
    is fully machine-checked.

  Still outside this theorem:
  - proving a concrete dense schedule / Lipschitz producer supplies
    `CountableScheduleCloseCertificate`;
  - gamma sampler expectation, deterministic quadrature, order-statistics,
    parameter estimation, and runtime mechanism-faithfulness.
-/


end

end FiniteGammaBridgeCertificate
