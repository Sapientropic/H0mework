import H0mework.Physics.NonlinearOrbit.Confinement

/-! Selector-independent local flow and continuation at an actually reached
state, using the same source Hamiltonian and phase generator. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
open Set Filter Metric
open scoped Topology

noncomputable section

variable {initial : PhaseSpace} {initialTime : ℝ}

theorem LocalOrbit.unique_on (first second : LocalOrbit initial initialTime) :
    EqOn first.curve second.curve (first.window ∩ second.window) := by
  intro time inside
  have distance : |time-initialTime| < min first.radius second.radius := by
    apply lt_min <;> rw [abs_lt]
    · constructor <;> linarith [inside.1.1, inside.1.2]
    · constructor <;> linarith [inside.2.1, inside.2.2]
  let radius := (min first.radius second.radius + |time-initialTime|)/2
  have rpositive : 0 < radius := by dsimp [radius]; linarith [abs_nonneg (time-initialTime)]
  have rsmall : radius < min first.radius second.radius := by dsimp [radius]; linarith
  have rlarge : |time-initialTime| < radius := by dsimp [radius]; linarith
  have contained : Icc (initialTime-radius) (initialTime+radius) ⊆ first.window ∩ second.window := by
    intro candidate belongs
    have firstBound := rsmall.trans_le (min_le_left first.radius second.radius)
    have secondBound := rsmall.trans_le (min_le_right first.radius second.radius)
    constructor <;> constructor <;> linarith [belongs.1, belongs.2]
  have continuous : ContinuousOn (fun t => (first.curve t, second.curve t))
      (Icc (initialTime-radius) (initialTime+radius)) := by
    intro candidate belongs
    exact ((first.evolves candidate (contained belongs).1).continuousAt.prodMk
      (second.evolves candidate (contained belongs).2).continuousAt).continuousWithinAt
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous
  obtain ⟨K, lipschitz⟩ := generator_contDiff.contDiffOn.exists_lipschitzOnWith
    (by decide) (convex_closedBall (0 : PhaseSpace) bound) (isCompact_closedBall (0 : PhaseSpace) bound)
  have firstBound (candidate : ℝ) (belongs : candidate ∈ Icc (initialTime-radius) (initialTime+radius)) :
      first.curve candidate ∈ closedBall (0 : PhaseSpace) bound := by
    simpa only [mem_closedBall, dist_zero_right] using
      (norm_fst_le (first.curve candidate, second.curve candidate)).trans (bounded candidate belongs)
  have secondBound (candidate : ℝ) (belongs : candidate ∈ Icc (initialTime-radius) (initialTime+radius)) :
      second.curve candidate ∈ closedBall (0 : PhaseSpace) bound := by
    simpa only [mem_closedBall, dist_zero_right] using
      (norm_snd_le (first.curve candidate, second.curve candidate)).trans (bounded candidate belongs)
  have same : EqOn first.curve second.curve (Icc (initialTime-radius) (initialTime+radius)) := by
    apply ODE_solution_unique_of_mem_Icc (v := fun _ => generator) (s := fun _ => closedBall (0 : PhaseSpace) bound)
      (K := K) (t₀ := initialTime)
    · exact fun _ _ => lipschitz
    · exact ⟨by linarith, by linarith⟩
    · exact continuous.fst
    · exact fun t ht => first.evolves t (contained (Ioo_subset_Icc_self ht)).1
    · exact fun t ht => firstBound t (Ioo_subset_Icc_self ht)
    · exact continuous.snd
    · exact fun t ht => second.evolves t (contained (Ioo_subset_Icc_self ht)).2
    · exact fun t ht => secondBound t (Ioo_subset_Icc_self ht)
    · exact first.starts.trans second.starts.symm
  apply same
  rw [abs_lt] at rlarge
  constructor <;> linarith [rlarge.1, rlarge.2]

def LocalOrbit.recenter (flow : LocalOrbit initial initialTime) (time : ℝ) (inside : time ∈ flow.window) :
    LocalOrbit (flow.curve time) time where
  radius := min (time-(initialTime-flow.radius)) ((initialTime+flow.radius)-time)/2
  positive := half_pos (lt_min (sub_pos.mpr inside.1) (sub_pos.mpr inside.2))
  curve := flow.curve
  starts := rfl
  evolves := by
    intro candidate belongs
    apply flow.evolves
    have leftBound := min_le_left (time-(initialTime-flow.radius)) ((initialTime+flow.radius)-time)
    have rightBound := min_le_right (time-(initialTime-flow.radius)) ((initialTime+flow.radius)-time)
    have positive := lt_min (sub_pos.mpr inside.1) (sub_pos.mpr inside.2)
    constructor <;> linarith [belongs.1, belongs.2]

structure Continuation (flow : LocalOrbit initial initialTime) (time : ℝ) where
  next : LocalOrbit (flow.curve time) time
  same_germ : flow.curve =ᶠ[𝓝 time] next.curve

theorem LocalOrbit.continuation_exists (flow : LocalOrbit initial initialTime) (time : ℝ)
    (inside : time ∈ flow.window) : Nonempty (Continuation flow time) := by
  obtain ⟨next⟩ := localOrbit_exists (flow.curve time) time
  exact ⟨⟨next, (flow.recenter time inside).unique_germ next⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
