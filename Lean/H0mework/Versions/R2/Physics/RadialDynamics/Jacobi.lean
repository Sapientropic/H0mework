import H0mework.Versions.R2.Physics.RadialDynamics.Action

/-! The canonical positive-frequency linear response of the source action.
This is its radial Jacobi dynamics, with unit canonical momentum impulse. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open Stage9C.Material.SpinPair

noncomputable section

def responseFrequency : ℝ := Real.sqrt (stiffness/inertia)

theorem responseFrequency_pos : 0 < responseFrequency :=
  Real.sqrt_pos.2 (div_pos stiffness_pos inertia_pos)

theorem responseFrequency_sq : responseFrequency^2 = stiffness/inertia :=
  Real.sq_sqrt (le_of_lt (div_pos stiffness_pos inertia_pos))

theorem responseFrequency_source : responseFrequency^2 = 6*gaugeScale^2/lapse^2 := by
  rw [responseFrequency_sq, stiffness_eq, inertia_eq]
  field_simp [ne_of_gt lapse_pos, sourceCoupling_eq]
  ring

theorem responseFrequency_source_value : responseFrequency^2 = 10 := by
  rw [responseFrequency_source, lapse_sq]
  norm_num [gaugeScale, div_pow, mul_pow, spinScale_sq]

def impulse (time : ℝ) : ℝ := Real.sin (responseFrequency*time)/(inertia*responseFrequency)
def impulseMomentum (time : ℝ) : ℝ := Real.cos (responseFrequency*time)
def impulseAcceleration (time : ℝ) : ℝ := -responseFrequency*Real.sin (responseFrequency*time)/inertia

theorem impulse_initial : impulse 0 = 0 ∧ impulseMomentum 0 = 1 := by
  simp [impulse, impulseMomentum]

theorem impulse_hasDerivAt (time : ℝ) :
    HasDerivAt impulse (impulseMomentum time/inertia) time := by
  unfold impulse
  convert (((hasDerivAt_id time).const_mul responseFrequency).sin).div_const
    (inertia*responseFrequency) using 1
  all_goals try rfl
  simp only [id_eq, mul_one]
  unfold impulseMomentum
  field_simp [ne_of_gt inertia_pos, ne_of_gt responseFrequency_pos]

theorem impulseVelocity_hasDerivAt (time : ℝ) :
    HasDerivAt (fun t => impulseMomentum t/inertia) (impulseAcceleration time) time := by
  unfold impulseMomentum impulseAcceleration
  convert (((hasDerivAt_id time).const_mul responseFrequency).cos).div_const inertia using 1
  all_goals first | rfl | simp only [id_eq]; ring

theorem impulse_equation (time : ℝ) :
    inertia*impulseAcceleration time + stiffness*impulse time = 0 := by
  unfold impulseAcceleration impulse
  have square := responseFrequency_sq
  field_simp [ne_of_gt inertia_pos] at square
  field_simp [ne_of_gt inertia_pos, ne_of_gt responseFrequency_pos]
  rw [← square]
  ring

theorem force_hasDerivAt (displacement acceleration : ℝ) :
    HasDerivAt (fun parameter => force (gaugeScale+parameter*displacement) (parameter*acceleration))
      ((2/3:ℝ)*(inertia*acceleration+stiffness*displacement)) 0 := by
  unfold force
  have first := (((hasDerivAt_id (0:ℝ)).mul_const acceleration).const_mul lapse).div_const sourceCoupling
  have second := ((((hasDerivAt_id (0:ℝ)).mul_const displacement).const_add gaugeScale).pow 3).const_mul 2
    |>.div_const (sourceCoupling*lapse)
  convert (first.add second).sub_const (4*lapse*spinScale) using 1
  all_goals try rfl
  simp only [id_eq, zero_mul, add_zero, one_mul]
  rw [inertia_eq, stiffness_eq]
  ring

theorem linearized_source_euler (time : ℝ) :
    HasDerivAt (fun parameter =>
      force (gaugeScale+parameter*impulse time) (parameter*impulseAcceleration time)) 0 0 := by
  simpa [impulse_equation] using force_hasDerivAt (impulse time) (impulseAcceleration time)

def quadraticEnergy (displacement canonicalMomentum : ℝ) : ℝ :=
  stiffness/2*displacement^2 + canonicalMomentum^2/(2*inertia)

theorem energy_expansion (parameter displacement canonicalMomentum : ℝ) :
    energy (gaugeScale+parameter*displacement) (parameter*canonicalMomentum) = energy gaugeScale 0 +
      parameter^2*quadraticEnergy displacement canonicalMomentum +
      3*gaugeScale/(sourceCoupling*lapse)*parameter^3*displacement^3 +
      3/(4*sourceCoupling*lapse)*parameter^4*displacement^4 := by
  rw [energy_eq, energy_eq, potential_eq, potential_eq]
  unfold quadraticEnergy
  rw [stiffness_eq]
  have stationary := equilibrium
  rw [restoring_eq] at stationary
  linear_combination parameter*displacement*stationary

theorem quadraticEnergy_position (displacement canonicalMomentum : ℝ) :
    HasDerivAt (fun q => quadraticEnergy q canonicalMomentum)
      (stiffness*displacement) displacement := by
  unfold quadraticEnergy
  convert (((hasDerivAt_id displacement).pow 2).const_mul (stiffness/2)).add_const
    (canonicalMomentum^2/(2*inertia)) using 1
  all_goals first | rfl | simp only [id_eq]; ring

theorem quadraticEnergy_momentum (displacement canonicalMomentum : ℝ) :
    HasDerivAt (quadraticEnergy displacement) (canonicalMomentum/inertia) canonicalMomentum := by
  unfold quadraticEnergy
  convert (((hasDerivAt_id canonicalMomentum).pow 2).div_const (2*inertia)).const_add
    (stiffness/2*displacement^2) using 1
  all_goals first | rfl | simp only [id_eq]; ring

theorem impulseMomentum_hasDerivAt (time : ℝ) :
    HasDerivAt impulseMomentum (-stiffness*impulse time) time := by
  have raw := ((hasDerivAt_id time).const_mul responseFrequency).cos
  have coefficient : -Real.sin (responseFrequency*time)*responseFrequency = -stiffness*impulse time := by
    unfold impulse
    have square := responseFrequency_sq
    field_simp [ne_of_gt inertia_pos] at square
    field_simp [ne_of_gt inertia_pos, ne_of_gt responseFrequency_pos]
    rw [← square]
    ring
  unfold impulseMomentum
  simpa only [id_eq, mul_one, coefficient] using raw

theorem impulse_energy (time : ℝ) :
    quadraticEnergy (impulse time) (impulseMomentum time) = 1/(2*inertia) := by
  unfold quadraticEnergy impulse impulseMomentum
  have square := responseFrequency_sq
  field_simp [ne_of_gt inertia_pos] at square
  field_simp [ne_of_gt inertia_pos, ne_of_gt responseFrequency_pos]
  rw [← square]
  linear_combination (responseFrequency^2*inertia) * Real.sin_sq_add_cos_sq (responseFrequency*time)

theorem canonical_response (time : ℝ) :
    HasDerivAt impulse
      (deriv (quadraticEnergy (impulse time)) (impulseMomentum time)) time ∧
    HasDerivAt impulseMomentum
      (-deriv (fun q => quadraticEnergy q (impulseMomentum time)) (impulse time)) time := by
  rw [(quadraticEnergy_momentum _ _).deriv, (quadraticEnergy_position _ _).deriv]
  exact ⟨impulse_hasDerivAt time, by simpa only [neg_mul] using impulseMomentum_hasDerivAt time⟩

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
