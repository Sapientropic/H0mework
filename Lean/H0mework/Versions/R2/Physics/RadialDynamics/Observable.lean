import H0mework.Versions.R2.Physics.RadialDynamics.MatterAction
import H0mework.Versions.R2.Physics.MatrixResponse.Value

/-! The physical full-mother helicity, evaluated on the source-action radial
response. The response is differentiated from that same field observable. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

def physicalValue (parameter time : ℝ) : ℝ :=
  (MatrixResponse.value (responseProfile parameter time • (1 : MatrixResponse.Coefficients))).re

def helicityResponse (time : ℝ) : ℝ := deriv (fun parameter => physicalValue parameter time) 0

theorem radial_connection_matrix (parameter : ℝ) (point : BasePoint) (axis : Fin 3) :
    MatrixResponse.connection (responseProfile parameter (point 0) • (1 : MatrixResponse.Coefficients)) axis =
      p286LieBlockEmbed ((radialWrite (responseProfile parameter)).gaugeConnection point axis.succ) := by
  fin_cases axis <;> simp [MatrixResponse.connection, MatrixResponse.mother, MatrixResponse.color,
    radialWrite, gaugePotential]

theorem radial_magnetic_matrix (parameter : ℝ) (point : BasePoint) (axis : Fin 3) :
    MatrixResponse.magnetic (responseProfile parameter (point 0) • (1 : MatrixResponse.Coefficients)) axis =
      p286LieBlockEmbed (holonomicGaugeCurvature (radialWrite (responseProfile parameter)) point (magneticPair axis)) := by
  rw [radialWrite_curvature _ _ _ (responseProfile_hasDerivAt parameter (point 0)),
    MatrixResponse.magnetic_coefficients]
  fin_cases axis <;>
    simp [MatrixResponse.mother, MatrixResponse.color, MatrixResponse.cofactors,
      cross_apply, radialCurvature, magneticPair, pow_two]

theorem physicalValue_field (parameter : ℝ) (point : BasePoint) :
    physicalValue parameter (point 0) =
      (Helicity.homogeneousHelicity
        (fun axis => p286LieBlockEmbed ((radialWrite (responseProfile parameter)).gaugeConnection point axis.succ))
        (fun axis => p286LieBlockEmbed (holonomicGaugeCurvature
          (radialWrite (responseProfile parameter)) point (magneticPair axis)))).re := by
  unfold physicalValue MatrixResponse.value
  congr 2
  · exact funext (radial_connection_matrix parameter point)
  · exact funext (radial_magnetic_matrix parameter point)

theorem physicalValue_eq (parameter time : ℝ) :
    physicalValue parameter time = 3*(responseProfile parameter time)^5 := by
  unfold physicalValue
  rw [MatrixResponse.value_scalar, Complex.ofReal_re]

theorem physicalValue_background (time : ℝ) : physicalValue 0 time = (Helicity.value 0).re := by
  rw [physicalValue_eq, Helicity.value_eq]
  simp [responseProfile]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem physicalValue_hasDerivAt (time : ℝ) :
    HasDerivAt (fun parameter => physicalValue parameter time) (15*gaugeScale^4*impulse time) 0 := by
  simp_rw [physicalValue_eq]
  unfold responseProfile
  convert ((((hasDerivAt_id (0:ℝ)).mul_const (impulse time)).const_add gaugeScale).pow 5).const_mul 3 using 1
  all_goals first | rfl | simp only [id_eq, zero_mul, add_zero, one_mul]; ring

theorem helicityResponse_eq (time : ℝ) : helicityResponse time = 15*gaugeScale^4*impulse time :=
  (physicalValue_hasDerivAt time).deriv

theorem helicityResponse_hasDerivAt (time : ℝ) :
    HasDerivAt helicityResponse (15*gaugeScale^4*(impulseMomentum time/inertia)) time := by
  rw [show helicityResponse = fun t => 15*gaugeScale^4*impulse t from funext helicityResponse_eq]
  exact (impulse_hasDerivAt time).const_mul _

theorem helicityResponse_initial_velocity :
    0 < deriv helicityResponse 0 := by
  rw [(helicityResponse_hasDerivAt 0).deriv, impulse_initial.2]
  exact mul_pos (mul_pos (by norm_num) (pow_pos gaugeScale_pos 4)) (div_pos (by norm_num) inertia_pos)

theorem helicityResponse_nonconstant : ¬ ∃ value : ℝ, helicityResponse = fun _ => value := by
  rintro ⟨value, constant⟩
  have nonzero := helicityResponse_initial_velocity
  rw [constant, deriv_const] at nonzero
  exact lt_irrefl 0 nonzero

theorem helicityResponse_acceleration (time : ℝ) :
    HasDerivAt (fun t => deriv helicityResponse t)
      (15*gaugeScale^4*impulseAcceleration time) time := by
  have velocities : (fun t => deriv helicityResponse t) =
      fun t => 15*gaugeScale^4*(impulseMomentum t/inertia) :=
    funext (fun t => (helicityResponse_hasDerivAt t).deriv)
  rw [velocities]
  exact (impulseVelocity_hasDerivAt time).const_mul _

theorem helicityResponse_oscillator (time : ℝ) :
    deriv (deriv helicityResponse) time + responseFrequency^2*helicityResponse time = 0 := by
  rw [(helicityResponse_acceleration time).deriv, helicityResponse_eq, responseFrequency_sq]
  have equation := impulse_equation time
  field_simp [ne_of_gt inertia_pos]
  linear_combination 15*gaugeScale^4*equation

theorem helicityResponse_quarter :
    0 < helicityResponse (Real.pi/(2*responseFrequency)) := by
  rw [helicityResponse_eq]
  unfold impulse
  have angle : responseFrequency*(Real.pi/(2*responseFrequency)) = Real.pi/2 := by
    field_simp [ne_of_gt responseFrequency_pos]
  rw [angle, Real.sin_pi_div_two]
  exact mul_pos (mul_pos (by norm_num) (pow_pos gaugeScale_pos 4))
    (div_pos (by norm_num) (mul_pos inertia_pos responseFrequency_pos))

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
