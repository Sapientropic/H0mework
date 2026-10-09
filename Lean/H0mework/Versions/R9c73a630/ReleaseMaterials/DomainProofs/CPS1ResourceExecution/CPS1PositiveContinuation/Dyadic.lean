import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositiveContinuation.Renewal

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositiveContinuation
noncomputable section
open CPS1Deformation CPS1ElectronicSource CPS1PositivePulse
open scoped Topology
variable {frame : CPS1Recycling.Frame}

def RenewingDyadic (state : Material frame) (index : Nat) : Prop :=
  ∃ next : Material frame × ElectronicPulse,
    state.pulse? (dyadicTime index) = .ok next ∧ PulseReady next.1

theorem exists_renewing_dyadic (state : Material frame) (ready : PulseReady state) :
    ∃ index, RenewingDyadic state index := by
  have powers : Filter.Tendsto dyadicTime Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,present⟩ := (powers.eventually (pulse_eventually_ready state ready)).exists
  exact ⟨index,present (dyadic_time_positive index).le⟩

def renewingIndex (state : Material frame) (ready : PulseReady state) : Nat := by
  classical
  exact Nat.find (exists_renewing_dyadic state ready)

theorem renewing_index_spec (state : Material frame) (ready : PulseReady state) :
    RenewingDyadic state (renewingIndex state ready) := by
  classical
  exact Nat.find_spec (exists_renewing_dyadic state ready)

theorem renewing_index_minimal (state : Material frame) (ready : PulseReady state)
    (index : Nat) (smaller : index < renewingIndex state ready) : ¬ RenewingDyadic state index := by
  classical
  exact Nat.find_min (exists_renewing_dyadic state ready) smaller

def renewingTime (state : Material frame) (ready : PulseReady state) : ℝ :=
  dyadicTime (renewingIndex state ready)

def renewingResult (state : Material frame) (ready : PulseReady state) : Material frame × ElectronicPulse :=
  match actual : state.pulse? (renewingTime state ready) with
  | .ok next => next
  | .error _ => False.elim (by
      obtain ⟨next,same,_⟩ := renewing_index_spec state ready
      change state.pulse? (renewingTime state ready) = .ok next at same
      rw [actual] at same
      cases same)

theorem renewing_actual (state : Material frame) (ready : PulseReady state) :
    state.pulse? (renewingTime state ready) = .ok (renewingResult state ready) := by
  unfold renewingResult
  split
  · assumption
  · obtain ⟨next,same,_⟩ := renewing_index_spec state ready
    change state.pulse? (renewingTime state ready) = .ok next at same
    contradiction

theorem renewing_ready (state : Material frame) (ready : PulseReady state) :
    PulseReady (renewingResult state ready).1 := by
  obtain ⟨next,actual,generated⟩ := renewing_index_spec state ready
  have same : next = renewingResult state ready :=
    Except.ok.inj (actual.symm.trans (renewing_actual state ready))
  exact same ▸ generated

theorem renewing_time_positive (state : Material frame) (ready : PulseReady state) :
    0 < renewingTime state ready := dyadic_time_positive _

theorem renewing_paid (state : Material frame) (ready : PulseReady state) :
    0 < (renewingResult state ready).1.reserve ∧
      (renewingResult state ready).1.energy+(renewingResult state ready).1.reserve = state.energy+state.reserve :=
  ⟨(renewing_ready state ready).budget,(pulse_paid state _ _ (renewing_actual state ready)).2.2.2⟩

end
end CPS1PositiveContinuation
