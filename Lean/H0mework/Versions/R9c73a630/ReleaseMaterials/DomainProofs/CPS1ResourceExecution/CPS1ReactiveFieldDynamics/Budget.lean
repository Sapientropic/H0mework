import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Response
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Energy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveFieldDynamics
noncomputable section
open scoped Topology Matrix.Norms.Elementwise

/-- The full nonlinear stored energy is recomputed after the same-source response. -/
def energyDelta (state : Snapshot) (time : ℝ) : ℝ :=
  (response state time).energy-state.energy

def paidResponse (state : Snapshot) (time : ℝ) : Snapshot :=
  (response state time).reprice (state.reserve-energyDelta state time)

theorem response_energy_continuous (state : Snapshot) (point : ℝ) :
    ContinuousAt (fun time : ℝ => (response state time).energy) point := by
  simpa only [response] using!
    (actual_energy_continuous state).continuousAt.comp (response_occupation_continuous state point)

theorem energy_delta_continuous (state : Snapshot) (point : ℝ) :
    ContinuousAt (energyDelta state) point :=
  (response_energy_continuous state point).sub continuousAt_const

theorem energy_delta_zero (state : Snapshot) : energyDelta state 0 = 0 := by
  rw [energyDelta,response_zero,sub_self]

theorem paid_response_good (state : Snapshot) (good : state.Good) (time : ℝ) :
    (paidResponse state time).Good := response_good state good time

theorem paid_response_account (state : Snapshot) (time : ℝ) :
    (paidResponse state time).energy = (response state time).energy ∧
    (paidResponse state time).reserve = state.reserve-energyDelta state time ∧
    (paidResponse state time).account = state.account := by
  refine ⟨rfl,rfl,?_⟩
  change (response state time).energy+(state.reserve-energyDelta state time) = state.energy+state.reserve
  unfold energyDelta
  ring

theorem paid_response_source (state : Snapshot) (time : ℝ) :
    (paidResponse state time).primitive = state.primitive ∧
    (paidResponse state time).nuclei = state.nuclei ∧
    (paidResponse state time).waterOrigins = state.waterOrigins ∧
    (paidResponse state time).electronInertia = state.electronInertia ∧
    (paidResponse state time).Ne = state.Ne := ⟨rfl,rfl,rfl,rfl,rfl⟩

def dyadicTime (index : Nat) : ℝ := (1/2 : ℝ)^index

theorem dyadic_time_positive (index : Nat) : 0 < dyadicTime index := pow_pos (by norm_num) index

def AffordableDyadic (state : Snapshot) (index : Nat) : Prop :=
  energyDelta state (dyadicTime index) < state.reserve

theorem exists_affordable_dyadic (state : Snapshot) (margin : 0 < state.reserve) :
    ∃ index, AffordableDyadic state index := by
  have neighborhood : ∀ᶠ time in 𝓝 (0 : ℝ), energyDelta state time < state.reserve :=
    (energy_delta_continuous state 0).eventually_lt continuousAt_const (by
      rw [energy_delta_zero]
      exact margin)
  have powers : Filter.Tendsto dyadicTime Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,paid⟩ := (powers.eventually neighborhood).exists
  exact ⟨index,paid⟩

def affordableIndex (state : Snapshot) (margin : 0 < state.reserve) : Nat := by
  classical
  exact Nat.find (exists_affordable_dyadic state margin)

theorem affordable_index_spec (state : Snapshot) (margin : 0 < state.reserve) :
    AffordableDyadic state (affordableIndex state margin) := by
  classical
  exact Nat.find_spec (exists_affordable_dyadic state margin)

theorem affordable_index_minimal (state : Snapshot) (margin : 0 < state.reserve)
    (index : Nat) (smaller : index < affordableIndex state margin) : ¬ AffordableDyadic state index := by
  classical
  exact Nat.find_min (exists_affordable_dyadic state margin) smaller

def generatedTime (state : Snapshot) (margin : 0 < state.reserve) : ℝ :=
  dyadicTime (affordableIndex state margin)

def generatedResponse (state : Snapshot) (margin : 0 < state.reserve) : Snapshot :=
  paidResponse state (generatedTime state margin)

theorem generated_response_paid (state : Snapshot) (good : state.Good) (margin : 0 < state.reserve) :
    0 < generatedTime state margin ∧ (generatedResponse state margin).Good ∧
    0 < (generatedResponse state margin).reserve ∧
    (generatedResponse state margin).account = state.account ∧
    (generatedResponse state margin).Ne = state.Ne := by
  exact ⟨dyadic_time_positive _,paid_response_good state good _,
    sub_pos.mpr (affordable_index_spec state margin),(paid_response_account state _).2.2,rfl⟩

end
end CPS1ReactiveFieldDynamics
