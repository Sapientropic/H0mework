import H0mework.Realization.Relations.P222

/-!
# Proposition 223: dense/Lipschitz producers for P222 close certificates

P222 made the all-real-time bridge honest by requiring a
`CountableScheduleCloseCertificate`.  This file proves a concrete analytic way
to produce that certificate: a countable schedule dense in the nonnegative
real time axis, together with a uniform Lipschitz bound for the finite mixtures
and the target, supplies P222's close certificate.

This is still not a gamma sampler theorem, quadrature theorem, or runtime
mechanism-faithfulness proof.  It closes the deterministic continuity adapter
between countable observation schedules and P219's all-time P170 facade.
-/

namespace FiniteGammaBridgeCertificate

open Filter
open scoped Topology

noncomputable section

/-! ## Dense countable schedules on nonnegative time -/

/-- A countable observation schedule whose listed times are dense in the
nonnegative real time axis. -/
structure DenseCountableObservationSchedule where
  Time : Type*
  inst : Countable Time
  time : Time → ℝ
  nonneg : ∀ τ : Time, 0 ≤ time τ
  dense_nonneg :
    ∀ {t : ℝ}, 0 ≤ t → ∀ δ : ℝ, 0 < δ →
      ∃ τ : Time, dist t (time τ) < δ

attribute [instance] DenseCountableObservationSchedule.inst

/-- Forget the density witness and keep the countable observation schedule. -/
def DenseCountableObservationSchedule.toCountableObservationSchedule
    (schedule : DenseCountableObservationSchedule) :
    CountableObservationSchedule where
  Time := schedule.Time
  inst := by infer_instance
  time := schedule.time
  nonneg := schedule.nonneg

/-! ## Uniform Lipschitz mesh certificates -/

/-- A schedule mesh certificate tuned to a Lipschitz constant `L`.

The producer promises that for every nonnegative time and error budget, some
scheduled time is close enough that a function with Lipschitz constant `L`
incurs less than `ε / 3` error. -/
structure CountableScheduleLipschitzMeshCertificate
    (schedule : CountableObservationSchedule) (L : ℝ) where
  mesh :
    ∀ {time : ℝ}, 0 ≤ time → ∀ ε : ℝ, 0 < ε →
      ∃ τ : schedule.Time,
        L * dist time (schedule.time τ) < ε / 3

/-- THEOREM 1: density of the observation schedule produces the Lipschitz mesh
certificate for every nonnegative Lipschitz constant. -/
theorem CountableScheduleLipschitzMeshCertificate.ofDense
    (schedule : DenseCountableObservationSchedule)
    {L : ℝ} (hL : 0 ≤ L) :
    CountableScheduleLipschitzMeshCertificate
      schedule.toCountableObservationSchedule L where
  mesh := by
    intro time htime ε hε
    by_cases hLzero : L = 0
    · have hone : (0 : ℝ) < 1 := by norm_num
      rcases schedule.dense_nonneg htime 1 hone with ⟨τ, _hτ⟩
      refine ⟨τ, ?_⟩
      have hthird : 0 < ε / 3 := by linarith
      simpa [hLzero] using hthird
    · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
      have hden : 0 < 3 * L := by nlinarith
      have hδ : 0 < ε / (3 * L) := div_pos hε hden
      rcases schedule.dense_nonneg htime (ε / (3 * L)) hδ with
        ⟨τ, hτ⟩
      refine ⟨τ, ?_⟩
      have hmul : L * dist time (schedule.time τ) <
          L * (ε / (3 * L)) :=
        mul_lt_mul_of_pos_left hτ hLpos
      have hright : L * (ε / (3 * L)) = ε / 3 := by
        field_simp [hLpos.ne']
      simpa [DenseCountableObservationSchedule.toCountableObservationSchedule,
        hright] using hmul

/-- A uniform Lipschitz producer certificate for P222.

Both the finite-mixture family and the continuous target share the same
Lipschitz constant `L`, and the schedule supplies an `L`-mesh.  This is enough
to create P222's close certificate. -/
structure UniformLipschitzCountableScheduleCertificate
    (schedule : CountableObservationSchedule)
    (mixture : ℕ → ℝ → ℝ) (target : ℝ → ℝ) where
  L : ℝ
  L_nonneg : 0 ≤ L
  mixture_lipschitz :
    ∀ (N : ℕ) (s t : ℝ),
      dist (mixture N s) (mixture N t) ≤ L * dist s t
  target_lipschitz :
    ∀ s t : ℝ,
      dist (target s) (target t) ≤ L * dist s t
  schedule_mesh : CountableScheduleLipschitzMeshCertificate schedule L

/-- THEOREM 2: a uniform Lipschitz producer certificate supplies P222's close
certificate. -/
theorem UniformLipschitzCountableScheduleCertificate.toCloseCertificate
    {schedule : CountableObservationSchedule}
    {mixture : ℕ → ℝ → ℝ} {target : ℝ → ℝ}
    (cert : UniformLipschitzCountableScheduleCertificate
      schedule mixture target) :
    CountableScheduleCloseCertificate schedule mixture target where
  close := by
    intro time htime ε hε
    rcases cert.schedule_mesh.mesh htime ε hε with ⟨τ, hτ⟩
    refine ⟨τ, ?_, ?_⟩
    · intro N
      exact lt_of_le_of_lt
        (cert.mixture_lipschitz N time (schedule.time τ)) hτ
    · have hτ' :
          cert.L * dist (schedule.time τ) time < ε / 3 := by
        simpa [dist_comm] using hτ
      exact lt_of_le_of_lt
        (cert.target_lipschitz (schedule.time τ) time) hτ'

/-- THEOREM 3: on a dense schedule, uniform Lipschitz bounds alone construct
P222's close certificate. -/
theorem CountableScheduleCloseCertificate.ofDenseUniformLipschitz
    (schedule : DenseCountableObservationSchedule)
    {mixture : ℕ → ℝ → ℝ} {target : ℝ → ℝ}
    {L : ℝ} (hL : 0 ≤ L)
    (hmix :
      ∀ (N : ℕ) (s t : ℝ),
        dist (mixture N s) (mixture N t) ≤ L * dist s t)
    (htarget :
      ∀ s t : ℝ,
        dist (target s) (target t) ≤ L * dist s t) :
    CountableScheduleCloseCertificate
      schedule.toCountableObservationSchedule mixture target :=
  (UniformLipschitzCountableScheduleCertificate.mk
    L hL hmix htarget
    (CountableScheduleLipschitzMeshCertificate.ofDense schedule hL)
  ).toCloseCertificate

/-! ## Gamma bridge constructors -/

/-- THEOREM 4: a countable schedule gamma bridge with a uniform Lipschitz
certificate compiles into P222's all-time gamma bridge. -/
def CountableScheduleToAllTimeGammaBridgeCertificate.ofUniformLipschitz
    {schedule : CountableObservationSchedule}
    {mixture : ℕ → ℝ → ℝ}
    {shape gammaRate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < gammaRate)
    (hconv :
      ∀ τ : schedule.Time,
        Tendsto
          (fun N : ℕ => mixture N (schedule.time τ))
          atTop
          (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate (schedule.time τ))))
    (lipCert : UniformLipschitzCountableScheduleCertificate schedule mixture
      (GammaMixtureForgetting.normalizedGammaLaplace shape gammaRate)) :
    CountableScheduleToAllTimeGammaBridgeCertificate schedule where
  mixture := mixture
  shape := shape
  gammaRate := gammaRate
  shape_pos := hshape
  gammaRate_pos := hrate
  schedule_tendsto_gamma := hconv
  close_to_schedule := lipCert.toCloseCertificate

/-- THEOREM 5: dense schedule + uniform Lipschitz bounds + scheduled gamma
convergence compiles into P222's all-time gamma bridge. -/
def CountableScheduleToAllTimeGammaBridgeCertificate.ofDenseUniformLipschitz
    (schedule : DenseCountableObservationSchedule)
    {mixture : ℕ → ℝ → ℝ}
    {shape gammaRate L : ℝ}
    (hshape : 0 < shape) (hrate : 0 < gammaRate) (hL : 0 ≤ L)
    (hconv :
      ∀ τ : schedule.Time,
        Tendsto
          (fun N : ℕ => mixture N (schedule.time τ))
          atTop
          (𝓝 (GammaMixtureForgetting.normalizedGammaLaplace
            shape gammaRate (schedule.time τ))))
    (hmix :
      ∀ (N : ℕ) (s t : ℝ),
        dist (mixture N s) (mixture N t) ≤ L * dist s t)
    (htarget :
      ∀ s t : ℝ,
        dist
          (GammaMixtureForgetting.normalizedGammaLaplace shape gammaRate s)
          (GammaMixtureForgetting.normalizedGammaLaplace shape gammaRate t) ≤
            L * dist s t) :
    CountableScheduleToAllTimeGammaBridgeCertificate
      schedule.toCountableObservationSchedule :=
  CountableScheduleToAllTimeGammaBridgeCertificate.ofUniformLipschitz
    hshape hrate hconv
    (UniformLipschitzCountableScheduleCertificate.mk
      L hL hmix htarget
      (CountableScheduleLipschitzMeshCertificate.ofDense schedule hL))

/-!
  Summary:
  - P222's close certificate is no longer only a raw external obligation.
  - A dense nonnegative countable schedule plus a uniform Lipschitz bound for
    both the finite mixtures and the target produces it.
  - The resulting gamma-specific constructor feeds directly into P222/P219.

  Still outside this theorem:
  - proving a concrete gamma sampler, quadrature scheme, or runtime harness has
    the required uniform Lipschitz bound;
  - order-statistics, parameter estimation, and runtime mechanism-faithfulness.
-/


end

end FiniteGammaBridgeCertificate
