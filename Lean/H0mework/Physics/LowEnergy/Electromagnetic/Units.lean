import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Normalization laws for a current-contracted simple static pole. A full
response must supply this pole and its propagation speed before the ratio can
be used as an electromagnetic observable. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic
noncomputable section

/-- Fourier inversion of `residue / |k|²`, including the electron vertex twice. -/
def poleCoulomb (electronVertex residue : ℝ) : ℝ :=
  electronVertex ^ 2 * residue / (4 * Real.pi)

/-- The denominator uses the same action and spacetime coordinates as C. -/
def couplingRatio (coefficient actionUnit speed : ℝ) : ℝ :=
  coefficient / (actionUnit * speed)

def chargeInElectronUnits (weight electronWeight : ℝ) : ℝ := weight / electronWeight

/-- Changing the field coordinate rescales both its residue and its vertex. -/
theorem field_rescaling (vertex residue scale : ℝ) (nonzero : scale ≠ 0) :
    poleCoulomb (vertex / scale) (scale ^ 2 * residue) =
      poleCoulomb vertex residue := by
  unfold poleCoulomb
  field_simp [nonzero]

/-- A generator rescaling changes the electron weight and inverse kinetic
form together. The physically contracted pole is unchanged. -/
theorem generator_rescaling (vertex residue scale : ℝ) (nonzero : scale ≠ 0) :
    poleCoulomb (scale * vertex) (residue / scale ^ 2) =
      poleCoulomb vertex residue := by
  unfold poleCoulomb
  field_simp [nonzero]

theorem charge_rescaling (weight electronWeight scale : ℝ) (nonzero : scale ≠ 0) :
    chargeInElectronUnits (scale * weight) (scale * electronWeight) =
      chargeInElectronUnits weight electronWeight := by
  unfold chargeInElectronUnits
  exact mul_div_mul_left _ _ nonzero

/-- Fractional weights survive normalization against the specified electron. -/
theorem fractional_charge_preserved (electronWeight : ℝ) (nonzero : electronWeight ≠ 0) :
    chargeInElectronUnits (electronWeight / 3) electronWeight = 1 / 3 := by
  unfold chargeInElectronUnits
  field_simp [nonzero]

theorem electron_magnitude_unit (electronWeight : ℝ) (nonzero : electronWeight ≠ 0) :
    |chargeInElectronUnits electronWeight electronWeight| = 1 := by
  simp [chargeInElectronUnits, nonzero]

/-- E, L and T are numerical unit sizes. All three physical quantities are
converted together; no reference mass or measured coupling enters. -/
theorem spacetime_units (C hbar speed energyUnit lengthUnit timeUnit : ℝ)
    (energy_nonzero : energyUnit ≠ 0) (length_nonzero : lengthUnit ≠ 0)
    (time_nonzero : timeUnit ≠ 0) :
    couplingRatio (C / (energyUnit * lengthUnit))
      (hbar / (energyUnit * timeUnit)) (speed * timeUnit / lengthUnit) =
      couplingRatio C hbar speed := by
  unfold couplingRatio
  field_simp [energy_nonzero, length_nonzero, time_nonzero]

theorem whole_action_rescaling (C hbar speed scale : ℝ) (nonzero : scale ≠ 0) :
    couplingRatio (scale * C) (scale * hbar) speed = couplingRatio C hbar speed := by
  unfold couplingRatio
  rw [mul_assoc]
  exact mul_div_mul_left _ _ nonzero

/-- The Coulomb coefficient already includes Fourier inversion's 4 pi. -/
theorem pole_ratio (vertex residue hbar speed : ℝ) :
    couplingRatio (poleCoulomb vertex residue) hbar speed =
      vertex ^ 2 * residue / (4 * Real.pi * hbar * speed) := by
  unfold couplingRatio poleCoulomb
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic
