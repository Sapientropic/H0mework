import H0mework.Physics.Helicity.Action

/-! The helicity/current response consumes the previously generated source
ground sector and exact phase flow. Its weight is calculated from the full
field action's occupied eigenvalue. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix MeasureTheory
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF

noncomputable section

def transferScale : ℝ := amplitude / curvatureScale ^ 3

theorem transferScale_pos : 0 < transferScale :=
  div_pos amplitude_pos (pow_pos curvatureScale_pos 3)

theorem observable_eq_scaled_cubic (point : BasePoint) :
    observable point = (transferScale : ℂ) • cubic point := by
  rw [observable_normalForm, cubic_normalForm, smul_smul]
  congr 1
  simp only [transferScale, Complex.ofReal_div, Complex.ofReal_pow]
  rw [div_mul_cancel₀ _ (pow_ne_zero 3 (by exact_mod_cast ne_of_gt curvatureScale_pos))]

def evolved (point displacement : BasePoint) : State.Observable :=
  star (Dynamics.unitary displacement : State.Observable) * observable point *
    (Dynamics.unitary displacement : State.Observable)

theorem evolved_eq_scaled (point displacement : BasePoint) :
    evolved point displacement = (transferScale : ℂ) • evolvedCubic point displacement := by
  rw [evolved, observable_eq_scaled_cubic, Matrix.mul_smul, Matrix.smul_mul]
  rfl

theorem vacuumConnected_smul (scalar : ℂ) (first second : State.Observable) :
    vacuumConnected (scalar • first) (scalar • second) =
      star scalar * scalar * vacuumConnected first second := by
  simp only [vacuumConnected, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    map_smul, smul_eq_mul, star_mul]
  ring

theorem transferScale_weight :
    star (transferScale : ℂ) * (transferScale : ℂ) * (curvatureScale : ℂ) ^ 6 = (amplitude : ℂ) ^ 2 := by
  simp [transferScale]
  field_simp [ne_of_gt curvatureScale_pos]

theorem connected_phase (point first second : BasePoint) :
    vacuumConnected (evolved point first) (evolved point second) =
      (amplitude : ℂ) ^ 2 * phase spectralFrequency (second - first) := by
  rw [evolved_eq_scaled, evolved_eq_scaled, vacuumConnected_smul, vacuumConnected_phase]
  calc
    _ = (star (transferScale : ℂ) * (transferScale : ℂ) * (curvatureScale : ℂ) ^ 6) *
        phase spectralFrequency (second - first) := by ring
    _ = _ := by rw [transferScale_weight]

def spectralMeasure : Measure ℝ := ENNReal.ofReal (amplitude ^ 2) • Measure.dirac spectralFrequency

theorem connected_spectralIntegral (point first second : BasePoint) :
    vacuumConnected (evolved point first) (evolved point second) =
      ∫ rate : ℝ, phase rate (second - first) ∂spectralMeasure := by
  rw [connected_phase, spectralMeasure, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (le_of_lt (pow_pos amplitude_pos 2)), Complex.real_smul, Complex.ofReal_pow]

theorem spectral_atom : spectralMeasure {spectralFrequency} = ENNReal.ofReal (amplitude ^ 2) := by
  simp [spectralMeasure]

theorem spectral_atom_nonzero : spectralMeasure {spectralFrequency} ≠ 0 := by
  rw [spectral_atom]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos amplitude_pos 2))

theorem spectral_outside : spectralMeasure {spectralFrequency}ᶜ = 0 := by
  simp [spectralMeasure]

theorem positive_gap (point : BasePoint) :
    (phaseHamiltonian + (frequency : ℂ) • 1) * (observable point * groundProjector) =
      (spectralFrequency : ℂ) • (observable point * groundProjector) := by
  rw [observable_eq_scaled_cubic, Matrix.smul_mul, Matrix.mul_smul, cubic_positive_gap]
  exact smul_comm _ _ _

theorem excitation_nonzero (point : BasePoint) : observable point * groundProjector ≠ 0 := by
  rw [observable_eq_scaled_cubic, Matrix.smul_mul]
  exact smul_ne_zero (by exact_mod_cast ne_of_gt transferScale_pos) (cubic_excitation_nonzero point)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
