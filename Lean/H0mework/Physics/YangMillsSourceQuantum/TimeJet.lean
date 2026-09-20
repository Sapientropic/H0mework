import H0mework.Physics.YangMillsSourceQuantum.Response
import H0mework.Physics.GlobalOrbit.Acceptance

/-! On the original complete radial orbit, the physical matter time jet
reads the coupled gauge radius and momentum. The original clock is a probe
in this pairing, not the nonlinear orbit's generator. -/

set_option autoImplicit false
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF FullPairing
open Stage10.GaugeSpectrum.Global Stage10.GaugeSpectrum.Nonlinear
open Stage10.GaugeSpectrum
noncomputable section

private def phasePoint (angle : ℝ) : BasePoint := Stage9DEF.Dynamics.timeDisplacement (angle / frequency)

private theorem moving_prepared (angle : ℝ) :
    (1 / 2 : ℂ) • naturalCoordinates (Stage10.GaugeSpectrum.Dynamics.movingMatter angle) =
      prepared (phasePoint angle) := by
  have up : upperPhase (phasePoint angle) = Stage10.GaugeSpectrum.Dynamics.unitPhase angle := by
    simp only [upperPhase, phase, phasePoint, Stage9DEF.Dynamics.timeDisplacement_zero,
      Stage10.GaugeSpectrum.Dynamics.unitPhase, Complex.ofReal_div]
    congr 1
    field_simp [Complex.ofReal_ne_zero.mpr Stage9DEF.Dynamics.frequency_positive.ne']
  have down : lowerPhase (phasePoint angle) = Stage10.GaugeSpectrum.Dynamics.unitPhase (-angle) := by
    simp only [lowerPhase, phase, phasePoint, Stage9DEF.Dynamics.timeDisplacement_zero,
      Stage10.GaugeSpectrum.Dynamics.unitPhase, Complex.ofReal_div, Complex.ofReal_neg]
    congr 1
    field_simp [Complex.ofReal_ne_zero.mpr Stage9DEF.Dynamics.frequency_positive.ne']
  have actual : Stage10.GaugeSpectrum.Dynamics.movingMatter angle =
      Stage9C.Material.SpinPair.actual.matter (phasePoint angle) := by
    rw [actual_matter]
    change Stage10.GaugeSpectrum.Dynamics.movingMatter angle =
      spinPairMatter (upperPhase (phasePoint angle)) (lowerPhase (phasePoint angle))
    rw [up, down]
    rfl
  rw [actual, actual_eq_twice_prepared, smul_smul]
  norm_num

variable {impulse : ℝ} (trajectory : CompleteOrbit impulse)

def feature (t : ℝ) : Hilbert := (1 / 2 : ℂ) • naturalCoordinates
  (trajectory.configuration.matter (Stage9DEF.Dynamics.timeDisplacement t))

theorem feature_eq (t : ℝ) :
    feature trajectory t = prepared (phasePoint ((trajectory.curve t).2.2)) := by
  change (1 / 2 : ℂ) • naturalCoordinates (Stage10.GaugeSpectrum.Dynamics.movingMatter
    ((trajectory.curve (Stage9DEF.Dynamics.timeDisplacement t 0)).2.2)) = _
  rw [Stage9DEF.Dynamics.timeDisplacement_zero]
  exact moving_prepared _

theorem feature_norm (t : ℝ) : ‖feature trajectory t‖ = 1 := by
  rw [feature_eq]
  exact prepared_norm _

private theorem angle_derivative (t : ℝ) :
    HasDerivAt (fun r => (trajectory.curve r).2.2)
      (3*lapse/2*(spinScale-(trajectory.curve t).1)) t :=
  (trajectory.slice t).angle_derivative t (trajectory.slice_contains t)

theorem feature_derivative (t : ℝ) :
    HasDerivAt (feature trajectory)
      ((3*lapse/2*(spinScale-(trajectory.curve t).1)/frequency) •
        NativeSource.velocity (feature trajectory t)) t := by
  let angle := (trajectory.curve t).2.2
  have original := NativeSource.original_physical_input 0 (angle/frequency)
  have read := NativeSource.source_velocity (phasePoint angle)
  rw [Stage10.Runtime.tick_vector] at original read
  dsimp only [phasePoint] at read
  simp only [zero_add] at original
  rw [← read] at original
  change HasDerivAt (fun r : ℝ => prepared (Stage9DEF.Dynamics.timeDisplacement r))
    (NativeSource.velocity (prepared (phasePoint angle))) (angle/frequency) at original
  have scaled := original.scomp t ((angle_derivative trajectory t).div_const frequency)
  rw [← feature_eq trajectory t] at scaled
  convert! scaled using 1
  funext r
  exact feature_eq trajectory r

private theorem velocity_norm (v : Hilbert) :
    ‖NativeSource.velocity v‖ = frequency * ‖v‖ := by
  let J := Quantum.Time.centered NativeSource.time (-frequency)
    (Multiplicative.ofAdd Observation.darkTime)
  have same : NativeSource.velocity v = ((frequency : ℂ)*Complex.I) • J v := by
    apply PiLp.ext
    intro i
    change NativeSource.velocity v i = ((frequency : ℂ)*Complex.I) * J v i
    rw [NativeSource.velocity_apply]
    change ((spinRate i.1 : ℝ) : ℂ)*Complex.I*v i =
      ((frequency : ℂ)*Complex.I) *
        (Quantum.Time.centered NativeSource.time (-frequency)
          (Multiplicative.ofAdd Observation.darkTime) v) i
    rw [NativeSource.centered_dark_apply]
    unfold spinRate Stage9DEF.Dynamics.rate
    by_cases upper : i.1.val < 2 <;> simp [upper]
  rw [same, norm_smul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Stage9DEF.Dynamics.frequency_positive.le, Complex.norm_I, mul_one,
    J.norm_map]

def rateRead (t : ℝ) : ℝ :=
  (inner ℂ (NativeSource.velocity (feature trajectory t)) (deriv (feature trajectory) t)).re / frequency

theorem rateRead_eq (t : ℝ) :
    rateRead trajectory t = 3*lapse/2*(spinScale-(trajectory.curve t).1) := by
  rw [rateRead, (feature_derivative trajectory t).deriv, inner_smul_right_eq_smul]
  rw [Complex.real_smul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have square : (inner ℂ (NativeSource.velocity (feature trajectory t))
      (NativeSource.velocity (feature trajectory t))).re =
        ‖NativeSource.velocity (feature trajectory t)‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [square, velocity_norm, feature_norm, mul_one]
  field_simp [Stage9DEF.Dynamics.frequency_positive.ne']

theorem rateRead_derivative (t : ℝ) :
    HasDerivAt (rateRead trajectory)
      (-(3*lapse/2)*((trajectory.curve t).2.1/Stage10.GaugeSpectrum.Dynamics.inertia)) t := by
  have position := (trajectory.slice t).amplitude_derivative t (trajectory.slice_contains t)
  change HasDerivAt (fun r => (trajectory.curve r).1)
    ((trajectory.curve t).2.1/Stage10.GaugeSpectrum.Dynamics.inertia) t at position
  have generated := (position.const_sub spinScale).const_mul (3*lapse/2)
  convert! generated using 1
  · funext r
    exact rateRead_eq trajectory r
  · ring

def radiusRead (t : ℝ) : ℝ := spinScale - (2/(3*lapse))*rateRead trajectory t

def momentumRead (t : ℝ) : ℝ :=
  -(2*Stage10.GaugeSpectrum.Dynamics.inertia/(3*lapse))*deriv (rateRead trajectory) t

theorem radiusRead_eq (t : ℝ) : radiusRead trajectory t = (trajectory.curve t).1 := by
  rw [radiusRead, rateRead_eq]
  field_simp [lapse_pos.ne']
  ring

theorem momentumRead_eq (t : ℝ) : momentumRead trajectory t = (trajectory.curve t).2.1 := by
  rw [momentumRead, (rateRead_derivative trajectory t).deriv]
  field_simp [lapse_pos.ne', Stage10.GaugeSpectrum.Dynamics.inertia_pos.ne']

end
end SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet
