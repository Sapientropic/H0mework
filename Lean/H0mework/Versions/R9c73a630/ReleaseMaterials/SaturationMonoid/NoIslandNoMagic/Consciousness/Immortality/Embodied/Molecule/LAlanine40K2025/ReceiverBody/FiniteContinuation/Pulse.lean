import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Step

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
noncomputable section

def pulseMomentum (current : Material) (fraction : ℝ) : Configuration :=
  fun i => (1+(gainQ current : ℝ)*fraction)*momentum current i

def pulseReceiver (current : Material) (fraction : ℝ) : ℝ :=
  current.body.resource.momentum+nuclearKinetic (momentum current)-nuclearKinetic (pulseMomentum current fraction)

def pulseForce (current : Material) (t : ℝ) (i : Coordinate) : ℝ :=
  (gainQ current : ℝ)*FiniteActuation.progressRate t*momentum current i

def kineticRate (current : Material) (t : ℝ) : ℝ :=
  2*(1+(gainQ current : ℝ)*FiniteActuation.progress t)*
    ((gainQ current : ℝ)*FiniteActuation.progressRate t)*nuclearKinetic (momentum current)

def pulseHamiltonian (current : Material) (t : ℝ) (r p : Configuration) : ℝ :=
  nuclearKinetic (p-pulseMomentum current (FiniteActuation.progress t))+sourcePotential+
    nuclearKinetic (pulseMomentum current (FiniteActuation.progress t))-
    ∑ i, pulseForce current t i*(r i-sourcePosition i)

theorem pulse_kinetic (current : Material) (fraction : ℝ) :
    nuclearKinetic (pulseMomentum current fraction)=
      (1+(gainQ current : ℝ)*fraction)^2*nuclearKinetic (momentum current) :=
  FiniteActuation.kinetic_scale (momentum current) _

theorem momentum_endpoints (current : Material) :
    pulseMomentum current 0=momentum current ∧ pulseMomentum current 1=momentum (nextMaterial current) := by
  constructor
  · funext i; simp [pulseMomentum]
  · funext i; simp only [pulseMomentum,mul_one,next_momentum]

theorem receiver_endpoints (current : Material) (valid : Admissible current) :
    pulseReceiver current 0=current.body.resource.momentum ∧
    pulseReceiver current 1=(nextMaterial current).body.resource.momentum := by
  constructor
  · rw [pulseReceiver,(momentum_endpoints current).1]
    ring
  · rw [pulseReceiver,(momentum_endpoints current).2,next_kinetic_generated current valid,valid.kinetic]
    rfl

theorem pulse_stock (current : Material) (valid : Admissible current) (fraction : ℝ)
    (lo : 0 ≤ fraction) (hi : fraction ≤ 1) :
    current.body.resource.momentum/2 < pulseReceiver current fraction := by
  have gp : 0 < (gainQ current : ℝ) := Rat.cast_pos.mpr (gain_positive current valid)
  have kp : 0 < nuclearKinetic (momentum current) := by
    rw [valid.kinetic]
    exact Rat.cast_pos.mpr valid.positiveKinetic
  have gl : 0 ≤ (gainQ current : ℝ)*fraction := mul_nonneg gp.le lo
  have gh : (gainQ current : ℝ)*fraction ≤ (gainQ current : ℝ) := by nlinarith
  have sq : (1+(gainQ current : ℝ)*fraction)^2 ≤ (1+(gainQ current : ℝ))^2 := by nlinarith
  have cap := mul_le_mul_of_nonneg_right sq kp.le
  have target := next_stock current valid
  rw [← (receiver_endpoints current valid).2] at target
  rw [pulseReceiver,pulse_kinetic] at target ⊢
  simp only [mul_one] at target
  linarith

theorem momentum_derivative (current : Material) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => pulseMomentum current (FiniteActuation.progress time) i) (pulseForce current t i) t := by
  simpa only [pulseMomentum,pulseForce] using!
    (((FiniteActuation.progress_derivative t).const_mul (gainQ current : ℝ)).const_add 1).mul_const (momentum current i)

theorem energy_derivative (current : Material) (t : ℝ) :
    HasDerivAt (fun time => nuclearKinetic (pulseMomentum current (FiniteActuation.progress time))) (kineticRate current t) t := by
  simp_rw [pulse_kinetic]
  simpa [kineticRate] using!
    ((((FiniteActuation.progress_derivative t).const_mul (gainQ current : ℝ)).const_add 1).pow 2).mul_const
      (nuclearKinetic (momentum current))

theorem receiver_derivative (current : Material) (t : ℝ) :
    HasDerivAt (fun time => pulseReceiver current (FiniteActuation.progress time)) (-kineticRate current t) t := by
  simpa only [pulseReceiver,zero_sub] using!
    (hasDerivAt_const t (current.body.resource.momentum+nuclearKinetic (momentum current))).sub (energy_derivative current t)

theorem hamiltonian_energy (current : Material) (t : ℝ) :
    pulseHamiltonian current t sourcePosition (pulseMomentum current (FiniteActuation.progress t))=
      nuclearKinetic (pulseMomentum current (FiniteActuation.progress t))+sourcePotential := by
  simp [pulseHamiltonian,nuclearKinetic]
  ring

theorem pulse_energy_account (current : Material) (t : ℝ) :
    pulseReceiver current (FiniteActuation.progress t)+
      pulseHamiltonian current t sourcePosition (pulseMomentum current (FiniteActuation.progress t))=
    current.body.resource.momentum+nuclearKinetic (momentum current)+sourcePotential := by
  rw [hamiltonian_energy,pulseReceiver]
  ring

theorem pulse_clock_partial (current : Material) (t : ℝ) :
    HasDerivAt (fun time => pulseHamiltonian current time sourcePosition (pulseMomentum current (FiniteActuation.progress t)))
      (kineticRate current t) t := by
  have each (i : Coordinate) : HasDerivAt (fun time =>
      (pulseMomentum current (FiniteActuation.progress t) i-pulseMomentum current (FiniteActuation.progress time) i)^2/(2*mass i)) 0 t := by
    have hd := (((hasDerivAt_const t (pulseMomentum current (FiniteActuation.progress t) i)).sub
      (momentum_derivative current t i)).pow 2).div_const (2*mass i)
    simpa using! hd
  have covariant : HasDerivAt (fun time =>
      nuclearKinetic (pulseMomentum current (FiniteActuation.progress t)-pulseMomentum current (FiniteActuation.progress time))) 0 t := by
    simpa only [nuclearKinetic,Pi.sub_apply,Finset.sum_const_zero] using!
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => each i)
  simpa only [pulseHamiltonian,sub_self,mul_zero,Finset.sum_const_zero,sub_zero,zero_add] using!
    (covariant.add_const sourcePotential).add (energy_derivative current t)

theorem pulse_position_partial (current : Material) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => pulseHamiltonian current t
      (Function.update sourcePosition i (sourcePosition i+x)) (pulseMomentum current (FiniteActuation.progress t)))
        (-pulseForce current t i) 0 := by
  have normal (x : ℝ) : pulseHamiltonian current t
      (Function.update sourcePosition i (sourcePosition i+x)) (pulseMomentum current (FiniteActuation.progress t))=
      sourcePotential+nuclearKinetic (pulseMomentum current (FiniteActuation.progress t))-pulseForce current t i*x := by
    unfold pulseHamiltonian
    have entry (j : Coordinate) :
        pulseForce current t j*((Function.update sourcePosition i (sourcePosition i+x)) j-sourcePosition j)=
        if j=i then pulseForce current t i*x else 0 := by
      by_cases same : j=i
      · subst j; simp
      · simp [same]
    simp_rw [entry]
    simp [nuclearKinetic]
  simp_rw [normal]
  simpa using! (hasDerivAt_const (0 : ℝ)
    (sourcePotential+nuclearKinetic (pulseMomentum current (FiniteActuation.progress t)))).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul (pulseForce current t i))

theorem pulse_momentum_partial (current : Material) (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => pulseHamiltonian current t sourcePosition
      (Function.update (pulseMomentum current (FiniteActuation.progress t)) i (pulseMomentum current (FiniteActuation.progress t) i+x))) 0 0 := by
  have normal (momentum : Configuration) : pulseHamiltonian current t sourcePosition momentum=
      FiniteActuation.rampHamiltonian (pulseMomentum current (FiniteActuation.progress t)) 0 0 sourcePosition momentum := by
    rw [FiniteActuation.ramp_control_held]
    simp [pulseHamiltonian]
  simp_rw [normal]
  have raw := FiniteActuation.ramp_momentum_partial (pulseMomentum current (FiniteActuation.progress t)) 0 0 i
  simpa only [FiniteActuation.ramp_position_zero,FiniteActuation.ramp_momentum_zero,zero_mul,zero_div] using raw

theorem pulse_junctions (current : Material) (r p : Configuration) :
    pulseHamiltonian current 0 r p=FiniteActuation.rampHamiltonian (momentum current) 0 0 r p ∧
    pulseHamiltonian current duration r p=FiniteActuation.rampHamiltonian (pulseMomentum current 1) 0 0 r p := by
  have force0 : pulseForce current 0=0 := by funext i; simp [pulseForce,FiniteActuation.progress_rate_endpoints.1]
  have force1 : pulseForce current duration=0 := by funext i; simp [pulseForce,FiniteActuation.progress_rate_endpoints.2]
  have p0 : pulseMomentum current 0=momentum current := by funext i; simp [pulseMomentum]
  rw [FiniteActuation.ramp_control_held,FiniteActuation.ramp_control_held]
  simp [pulseHamiltonian,FiniteActuation.progress_endpoints.1,FiniteActuation.progress_endpoints.2,force0,force1,p0]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
