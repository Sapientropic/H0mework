import H0mework.Chemistry.LAlanineThermalDynamics.FiniteControllerFlow

/-! # Actual controller backreaction pays each bounded system-energy update -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Dynamics

open scoped Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

def systemEnergy (systemH : Matrix ι ι ℂ) (current : ControllerJoint ι) : ℝ :=
  Collision.energy systemH (systemReduce current)

def controllerEnergy (gap : ℝ) (current : ControllerJoint ι) : ℝ :=
  Collision.energy (controllerHamiltonian gap) (controllerReduce current)

theorem bareEnergy_split (systemH : Matrix ι ι ℂ) (gap : ℝ) (current : ControllerJoint ι) :
    Collision.energy (bareHamiltonian systemH gap) current =
      systemEnergy systemH current + controllerEnergy gap current :=
  jointEnergy_real_eq_reduced systemH (controllerHamiltonian gap) current

theorem bare_commutes_with_total (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (resonance : Commute (bareHamiltonian systemH gap) interaction) :
    Commute (bareHamiltonian systemH gap) (totalHamiltonian systemH gap interaction) :=
  (Commute.refl _).add_right resonance

theorem controller_pays_system_change (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian)
    (resonance : Commute (bareHamiltonian systemH gap) interaction) (time : ℝ) (current : ControllerJoint ι) :
    (systemEnergy systemH (coupledNext systemH gap interaction hH hV time current) - systemEnergy systemH current) +
      (controllerEnergy gap (coupledNext systemH gap interaction hH hV time current) - controllerEnergy gap current) = 0 := by
  have conserved := energy_of_commuting_observable systemH gap interaction hH hV time
    (bareHamiltonian systemH gap) current (bare_commutes_with_total systemH gap interaction resonance)
  rw [bareEnergy_split, bareEnergy_split] at conserved
  linarith

theorem interactionEnergy_conserved (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian)
    (resonance : Commute (bareHamiltonian systemH gap) interaction) (time : ℝ) (current : ControllerJoint ι) :
    Collision.energy interaction (coupledNext systemH gap interaction hH hV time current) =
      Collision.energy interaction current :=
  energy_of_commuting_observable systemH gap interaction hH hV time interaction current
    (resonance.symm.add_right (Commute.refl _))

def excitedController : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1]

/-- A product appears only at the explicit controller initialization. -/
def chargedInput (system : Matrix ι ι ℂ) : ControllerJoint ι :=
  Matrix.kronecker system excitedController

theorem excitedController_positive : excitedController.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp

theorem excitedController_trace : excitedController.trace = 1 := by
  norm_num [excitedController, Matrix.trace_diagonal, Fin.sum_univ_two]

omit [DecidableEq ι] in
theorem chargedInput_positive (system : Matrix ι ι ℂ) (positive : system.PosSemidef) :
    (chargedInput system).PosSemidef := positive.kronecker excitedController_positive

omit [DecidableEq ι] in
theorem chargedInput_trace (system : Matrix ι ι ℂ) (normalized : system.trace = 1) :
    (chargedInput system).trace = 1 := by
  simp only [chargedInput, Matrix.kronecker, Matrix.trace_kronecker, normalized,
    excitedController_trace, one_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem chargedInput_system (system : Matrix ι ι ℂ) : systemReduce (chargedInput system) = system := by
  rw [chargedInput, systemReduce_tensor, excitedController_trace, one_smul]

omit [DecidableEq ι] in
theorem chargedInput_controller (system : Matrix ι ι ℂ) (normalized : system.trace = 1) :
    controllerReduce (chargedInput system) = excitedController := by
  rw [chargedInput, controllerReduce_tensor, normalized, one_smul]

def excitedProbability (current : ControllerJoint ι) : ℝ := ∑ i, (current (i, 1) (i, 1)).re

omit [DecidableEq ι] in
theorem controllerEnergy_eq_probability (gap : ℝ) (current : ControllerJoint ι) :
    controllerEnergy gap current = gap * excitedProbability current := by
  have entry : controllerReduce current 1 1 = ∑ i, current (i, 1) (i, 1) := rfl
  simp [controllerEnergy, controllerHamiltonian, Collision.energy, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.diagonal_mul, entry, excitedProbability, Complex.re_sum, Complex.mul_re]

omit [DecidableEq ι] in
theorem excitedProbability_range (current : ControllerJoint ι) (positive : current.PosSemidef)
    (normalized : current.trace = 1) : 0 ≤ excitedProbability current ∧ excitedProbability current ≤ 1 := by
  have diagonal (i : ι × Fin 2) : 0 ≤ (current i i).re :=
    (Complex.nonneg_iff.mp positive.diag_nonneg).1
  have first : 0 ≤ ∑ i, (current (i, 0) (i, 0)).re := Finset.sum_nonneg (fun i _ => diagonal (i, 0))
  have second : 0 ≤ excitedProbability current := Finset.sum_nonneg (fun i _ => diagonal (i, 1))
  have total := congrArg Complex.re normalized
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
    Fin.sum_univ_two, Finset.sum_add_distrib, Complex.add_re, Complex.re_sum, Complex.one_re] at total
  exact ⟨second, by change (∑ i, (current (i, 1) (i, 1)).re) ≤ 1; linarith⟩

omit [DecidableEq ι] in
theorem controllerEnergy_range (gap : ℝ) (gapNonnegative : 0 ≤ gap) (current : ControllerJoint ι)
    (positive : current.PosSemidef) (normalized : current.trace = 1) :
    0 ≤ controllerEnergy gap current ∧ controllerEnergy gap current ≤ gap := by
  rw [controllerEnergy_eq_probability]
  have probability := excitedProbability_range current positive normalized
  exact ⟨mul_nonneg gapNonnegative probability.1,
    (mul_le_mul_of_nonneg_left probability.2 gapNonnegative).trans_eq (mul_one gap)⟩

omit [DecidableEq ι] in
theorem chargedInput_controllerEnergy (gap : ℝ) (system : Matrix ι ι ℂ) (normalized : system.trace = 1) :
    controllerEnergy gap (chargedInput system) = gap := by
  unfold controllerEnergy
  rw [chargedInput_controller system normalized]
  simp [Collision.energy, controllerHamiltonian, excitedController, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two]

/-- Every current carries its own remaining fuel; the initial gap is not reissued per step. -/
theorem current_controller_energy_bound (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian)
    (resonance : Commute (bareHamiltonian systemH gap) interaction) (time : ℝ)
    (current : ControllerJoint ι) (positive : current.PosSemidef) (normalized : current.trace = 1)
    (gapNonnegative : 0 ≤ gap) :
    controllerEnergy gap current - gap ≤
        systemEnergy systemH (coupledNext systemH gap interaction hH hV time current) - systemEnergy systemH current ∧
      systemEnergy systemH (coupledNext systemH gap interaction hH hV time current) - systemEnergy systemH current ≤
        controllerEnergy gap current := by
  have targetBound := controllerEnergy_range gap gapNonnegative _
    (coupledNext_positive systemH gap interaction hH hV time current positive)
    ((coupledNext_trace systemH gap interaction hH hV time current).trans normalized)
  have balance := controller_pays_system_change systemH gap interaction hH hV resonance time current
  constructor <;> linarith

theorem finite_controller_energy_bound (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian)
    (resonance : Commute (bareHamiltonian systemH gap) interaction) (time : ℝ)
    (system : Matrix ι ι ℂ) (positive : system.PosSemidef) (normalized : system.trace = 1)
    (gapNonnegative : 0 ≤ gap) :
    0 ≤ systemEnergy systemH (coupledNext systemH gap interaction hH hV time (chargedInput system)) -
        systemEnergy systemH (chargedInput system) ∧
      systemEnergy systemH (coupledNext systemH gap interaction hH hV time (chargedInput system)) -
        systemEnergy systemH (chargedInput system) ≤ gap := by
  simpa only [chargedInput_controllerEnergy gap system normalized, sub_self] using
    current_controller_energy_bound systemH gap interaction hH hV resonance time (chargedInput system)
      (chargedInput_positive system positive) (chargedInput_trace system normalized) gapNonnegative

theorem positive_supply_changes_controller (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian)
    (resonance : Commute (bareHamiltonian systemH gap) interaction) (time : ℝ) (current : ControllerJoint ι)
    (supplied : systemEnergy systemH current <
      systemEnergy systemH (coupledNext systemH gap interaction hH hV time current)) :
    controllerReduce (coupledNext systemH gap interaction hH hV time current) ≠ controllerReduce current := by
  intro unchanged
  have balance := controller_pays_system_change systemH gap interaction hH hV resonance time current
  simp only [controllerEnergy, unchanged, sub_self, add_zero] at balance
  linarith

theorem two_step_supply_le_current_fuel (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian)
    (resonance : Commute (bareHamiltonian systemH gap) interaction) (first second : ℝ)
    (current : ControllerJoint ι) (positive : current.PosSemidef) (normalized : current.trace = 1)
    (gapNonnegative : 0 ≤ gap) :
    systemEnergy systemH (coupledNext systemH gap interaction hH hV second
        (coupledNext systemH gap interaction hH hV first current)) - systemEnergy systemH current ≤
      controllerEnergy gap current := by
  rw [← coupledNext_add]
  exact (current_controller_energy_bound systemH gap interaction hH hV resonance (second + first)
    current positive normalized gapNonnegative).2

theorem positive_supply_no_charged_reset (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian)
    (resonance : Commute (bareHamiltonian systemH gap) interaction) (time : ℝ)
    (system : Matrix ι ι ℂ) (normalized : system.trace = 1)
    (supplied : systemEnergy systemH (chargedInput system) <
      systemEnergy systemH (coupledNext systemH gap interaction hH hV time (chargedInput system))) :
    controllerReduce (coupledNext systemH gap interaction hH hV time (chargedInput system)) ≠ excitedController := by
  rw [← chargedInput_controller system normalized]
  exact positive_supply_changes_controller systemH gap interaction hH hV resonance time _ supplied

end

end LAlanine40K2025.Thermal.Powered.Dynamics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
