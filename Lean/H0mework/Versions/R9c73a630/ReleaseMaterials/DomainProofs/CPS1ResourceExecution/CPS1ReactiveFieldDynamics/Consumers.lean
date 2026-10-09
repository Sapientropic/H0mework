import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Mouths
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Derivative
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.DensityChange

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveFieldDynamics
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

theorem source_coordinates_synthesis (state : Snapshot) :
    CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (raw state) * sourceCoefficient state = 1 := by
  classical
  have gram : CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (raw state) * sourceCoefficient state =
      Matrix.gram ℂ (basis state) := by
    ext first second
    change (∑ p, inner ℂ (basis state first) (raw state p)*sourceCoefficient state p second) =
      inner ℂ (basis state first) (basis state second)
    have generated : (∑ p, sourceCoefficient state p second • raw state p) = basis state second :=
      basis_jet_zero state second
    rw [← generated,inner_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [inner_smul_right,mul_comm]
  rw [gram,Matrix.gram_eq_one_iff_orthonormal.mpr (basis_orthonormal state)]

theorem paid_coordinates_actual (state : Snapshot) (time : ℝ) :
    coordinates (paidResponse state time) = responseCoordinates state time := by
  change CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (raw state) *
    (state.occupied+sourceCoefficient state*(responseCoordinates state time-coordinates state)) = _
  rw [Matrix.mul_add,← Matrix.mul_assoc,source_coordinates_synthesis,Matrix.one_mul]
  change coordinates state+(responseCoordinates state time-coordinates state) = _
  abel

theorem paid_density_actual (state : Snapshot) (time : ℝ) :
    sourceDensity (paidResponse state time) = responseDensity state time := by
  rw [sourceDensity,paid_coordinates_actual]
  rfl

inductive DensityBranch
  | commuting
  | changing
  deriving DecidableEq

def densityBranch (pulse : Pulse frame) : DensityBranch := by
  classical
  exact if sourceCommutator pulse.before.fields = 0 then .commuting else .changing

theorem pulse_density_branch (pulse : Pulse frame) (valid : pulse.Valid) :
    match densityBranch pulse with
    | .commuting => sourceCommutator pulse.before.fields = 0 ∧
        HEq (sourceDensity pulse.after.fields) (sourceDensity pulse.before.fields)
    | .changing => ¬ HEq (sourceDensity pulse.after.fields) (sourceDensity pulse.before.fields) := by
  classical
  by_cases same : sourceCommutator pulse.before.fields = 0
  · simp only [densityBranch,if_pos same]
    refine ⟨same,?_⟩
    rw [valid.2.1]
    exact heq_of_eq ((paid_density_actual pulse.before.fields pulse.time).trans
      (response_density_eq_of_commutator_zero pulse.before.fields pulse.time same))
  · simp only [densityBranch,if_neg same]
    rw [valid.2.1]
    intro equal
    have stored : sourceDensity (paidResponse pulse.before.fields pulse.time) = sourceDensity pulse.before.fields :=
      eq_of_heq equal
    rw [paid_density_actual] at stored
    exact response_density_ne_of_commutator pulse.before.fields pulse.time
      (ne_of_gt (dyadic_time_positive pulse.index)) same stored

theorem actual_generated_pulse (current next : NativeCursor frame) (pulse : Pulse frame)
    (actual : step current = .ok (next,pulse)) :
    pulse.Valid ∧ type_of% (pulse_paid pulse (step_generated current next pulse actual).2.2.2.2.2.1) ∧
    type_of% (response_coordinates_hasDerivAt pulse.before.fields) ∧
    type_of% (response_density_hasDerivAt pulse.before.fields) ∧
    type_of% (actual_response_energy_hasDerivAt pulse.before.fields) ∧
    type_of% (pulse_density_branch pulse (step_generated current next pulse actual).2.2.2.2.2.1) ∧
    type_of% (CPS1ReactiveField.Carried.active_whole pulse.after) := by
  have valid := (step_generated current next pulse actual).2.2.2.2.2.1
  exact ⟨valid,pulse_paid pulse valid,response_coordinates_hasDerivAt _,response_density_hasDerivAt _,
    actual_response_energy_hasDerivAt _,pulse_density_branch pulse valid,
    CPS1ReactiveField.Carried.active_whole _⟩

theorem actual_finite_pulses (current : NativeCursor frame) (depth : Nat) :
    ∀ (pulse : Pulse frame) (held : pulse ∈ (renew current depth).pulses),
      type_of% (pulse_paid pulse ((renew_whole current depth).2.2 pulse held)) ∧
      type_of% (pulse_density_branch pulse ((renew_whole current depth).2.2 pulse held)) ∧
      type_of% (actual_response_energy_hasDerivAt pulse.before.fields) ∧
      type_of% (CPS1ReactiveField.Carried.active_whole pulse.after) := by
  intro pulse held
  have valid := (renew_whole current depth).2.2 pulse held
  exact ⟨pulse_paid pulse valid,pulse_density_branch pulse valid,
    actual_response_energy_hasDerivAt _,CPS1ReactiveField.Carried.active_whole _⟩

theorem finite_whole_paid (current : NativeCursor frame) (depth : Nat) (ready : Ready current) :
    type_of% (renew_ready current depth ready) ∧ type_of% (renew_endpoint current depth ready) ∧
    type_of% (renew_whole current depth) ∧ type_of% (actual_finite_pulses current depth) :=
  ⟨renew_ready current depth ready,renew_endpoint current depth ready,renew_whole current depth,
    actual_finite_pulses current depth⟩

end
end CPS1ReactiveFieldDynamics
