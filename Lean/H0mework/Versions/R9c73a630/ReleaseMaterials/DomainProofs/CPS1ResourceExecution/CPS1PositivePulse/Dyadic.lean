import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.SuccessNeighborhood
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositivePulse
noncomputable section
open CPS1Deformation CPS1ElectronicSource
open scoped Topology
variable {frame : CPS1Recycling.Frame}

structure PulseReady (state : Material frame) : Prop where
  good : Good state
  gathered : CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.currentJoint)
    state.currentJoint.rows = .ok state.currentNodes
  ready : CPS1AtomicDynamics.Body.ready state.currentNodes
  nuclearReady : CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference state.positions)
  mass : ∀ nuclear, 0 < CPS1MolecularFrame.inertia state.reference nuclear
  unit : IsUnit (gramAt state.reference state.positions)
  budget : 0 < state.reserve

def dyadicTime (index : Nat) : ℝ := (1/2 : ℝ) ^ index

theorem dyadic_time_positive (index : Nat) : 0 < dyadicTime index := pow_pos (by norm_num) index

def SuccessfulDyadic (state : Material frame) (index : Nat) : Prop :=
  ∃ next : Material frame × ElectronicPulse, state.pulse? (dyadicTime index) = .ok next

theorem exists_successful_dyadic (state : Material frame) (ready : PulseReady state) :
    ∃ index, SuccessfulDyadic state index := by
  have neighborhood := pulse_eventually_success state ready.good ready.gathered ready.ready
    ready.nuclearReady ready.mass ready.unit ready.budget
  have powers : Filter.Tendsto dyadicTime Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,present⟩ := (powers.eventually neighborhood).exists
  exact ⟨index,present (dyadic_time_positive index).le⟩

def generatedDyadicIndex (state : Material frame) (ready : PulseReady state) : Nat := by
  classical
  exact Nat.find (exists_successful_dyadic state ready)

theorem generated_dyadic_success (state : Material frame) (ready : PulseReady state) :
    SuccessfulDyadic state (generatedDyadicIndex state ready) := by
  classical
  exact Nat.find_spec (exists_successful_dyadic state ready)

theorem generated_dyadic_minimal (state : Material frame) (ready : PulseReady state)
    (index : Nat) (smaller : index < generatedDyadicIndex state ready) :
    ¬ SuccessfulDyadic state index := by
  classical
  exact Nat.find_min (exists_successful_dyadic state ready) smaller

/-- Read the original deterministic response; no representation or future endpoint is selected. -/
def generatedDyadicResult (state : Material frame) (ready : PulseReady state) : Material frame × ElectronicPulse :=
  match actual : state.pulse? (dyadicTime (generatedDyadicIndex state ready)) with
  | .ok next => next
  | .error _ => False.elim (by
      obtain ⟨next,same⟩ := generated_dyadic_success state ready
      rw [actual] at same
      cases same)

theorem generated_dyadic_actual (state : Material frame) (ready : PulseReady state) :
    state.pulse? (dyadicTime (generatedDyadicIndex state ready)) = .ok (generatedDyadicResult state ready) := by
  unfold generatedDyadicResult
  split
  · assumption
  · obtain ⟨next,same⟩ := generated_dyadic_success state ready
    contradiction

theorem generated_dyadic_good (state : Material frame) (ready : PulseReady state) :
    Good (generatedDyadicResult state ready).1 :=
  pulse_good state (generatedDyadicResult state ready) (dyadicTime (generatedDyadicIndex state ready))
    (generated_dyadic_actual state ready)

end
end CPS1PositivePulse
