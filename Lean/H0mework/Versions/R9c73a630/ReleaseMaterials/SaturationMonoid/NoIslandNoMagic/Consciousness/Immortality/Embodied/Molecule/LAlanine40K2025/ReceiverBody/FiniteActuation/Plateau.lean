import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.NativeRamp

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
noncomputable section

def progressRate (t : ℝ) : ℝ := 6*(t/duration)*(1-t/duration)/duration
def plateauForce (t : ℝ) (i : Coordinate) : ℝ := gain*progressRate t*initialMomentum i

theorem progress_derivative (t : ℝ) : HasDerivAt progress (progressRate t) t := by
  have unit := (hasDerivAt_id t).div_const duration
  convert ((unit.pow 2).const_mul 3).sub ((unit.pow 3).const_mul 2) using 1
  all_goals first | rfl | (dsimp [progress,progressRate]; ring)

theorem progress_rate_endpoints : progressRate 0=0 ∧ progressRate duration=0 := by
  simp [progressRate,ne_of_gt duration_positive]

theorem plateau_momentum_time_derivative (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun time => plateauMomentum (progress time) i) (plateauForce t i) t := by
  simpa only [plateauMomentum,plateauForce] using!
    (((progress_derivative t).const_mul gain).const_add 1).mul_const (initialMomentum i)

def kineticRate (t : ℝ) : ℝ :=
  2*(1+gain*progress t)*(gain*progressRate t)*initialKinetic

theorem plateau_energy_derivative (t : ℝ) :
    HasDerivAt (fun time => nuclearKinetic (plateauMomentum (progress time))) (kineticRate t) t := by
  simp_rw [plateau_kinetic]
  simpa [kineticRate] using!
    ((((progress_derivative t).const_mul gain).const_add 1).pow 2).mul_const initialKinetic

theorem plateau_receiver_derivative (t : ℝ) :
    HasDerivAt (fun time => plateauReceiver (progress time)) (-kineticRate t) t := by
  simpa only [plateauReceiver,zero_sub] using!
    (hasDerivAt_const t (initialReceiver+initialKinetic)).sub (plateau_energy_derivative t)

def plateauHamiltonian (t : ℝ) (r momentum : Configuration) : ℝ :=
  nuclearKinetic (momentum-plateauMomentum (progress t))+sourcePotential+
    nuclearKinetic (plateauMomentum (progress t))-
    ∑ i, plateauForce t i*(r i-sourcePosition i)

theorem plateau_hamiltonian_energy (t : ℝ) :
    plateauHamiltonian t sourcePosition (plateauMomentum (progress t))=
      nuclearKinetic (plateauMomentum (progress t))+sourcePotential := by
  simp [plateauHamiltonian,nuclearKinetic]
  ring

theorem plateau_account (t : ℝ) :
    plateauReceiver (progress t)+plateauHamiltonian t sourcePosition (plateauMomentum (progress t))=
      initialReceiver+initialKinetic+sourcePotential := by
  rw [plateau_hamiltonian_energy,plateauReceiver]
  ring

theorem plateau_position_partial (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => plateauHamiltonian t
      (Function.update sourcePosition i (sourcePosition i+x)) (plateauMomentum (progress t)))
        (-plateauForce t i) 0 := by
  have normal (x : ℝ) : plateauHamiltonian t
      (Function.update sourcePosition i (sourcePosition i+x)) (plateauMomentum (progress t))=
      sourcePotential+nuclearKinetic (plateauMomentum (progress t))-plateauForce t i*x := by
    unfold plateauHamiltonian
    have entry (j : Coordinate) :
        plateauForce t j*((Function.update sourcePosition i (sourcePosition i+x)) j-sourcePosition j)=
        if j=i then plateauForce t i*x else 0 := by
      by_cases same : j=i
      · subst j; simp
      · simp [same]
    simp_rw [entry]
    simp [nuclearKinetic]
  simp_rw [normal]
  simpa using! (hasDerivAt_const (0 : ℝ)
    (sourcePotential+nuclearKinetic (plateauMomentum (progress t)))).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul (plateauForce t i))

theorem plateau_momentum_partial (t : ℝ) (i : Coordinate) :
    HasDerivAt (fun x => plateauHamiltonian t sourcePosition
      (Function.update (plateauMomentum (progress t)) i (plateauMomentum (progress t) i+x))) 0 0 := by
  have normal (momentum : Configuration) : plateauHamiltonian t sourcePosition momentum=
      rampHamiltonian (plateauMomentum (progress t)) 0 0 sourcePosition momentum := by
    rw [ramp_control_held]
    simp [plateauHamiltonian]
  simp_rw [normal]
  have raw := ramp_momentum_partial (plateauMomentum (progress t)) 0 0 i
  simpa only [ramp_position_zero,ramp_momentum_zero,zero_mul,zero_div] using raw

theorem plateau_clock_partial (t : ℝ) :
    HasDerivAt (fun time => plateauHamiltonian time sourcePosition (plateauMomentum (progress t)))
      (kineticRate t) t := by
  have each (i : Coordinate) : HasDerivAt (fun time =>
      (plateauMomentum (progress t) i-plateauMomentum (progress time) i)^2/(2*mass i)) 0 t := by
    have hd := (((hasDerivAt_const t (plateauMomentum (progress t) i)).sub
      (plateau_momentum_time_derivative t i)).pow 2).div_const (2*mass i)
    simpa using! hd
  have covariant : HasDerivAt (fun time =>
      nuclearKinetic (plateauMomentum (progress t)-plateauMomentum (progress time))) 0 t := by
    simpa only [nuclearKinetic,Pi.sub_apply,Finset.sum_const_zero] using!
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => each i)
  simpa only [plateauHamiltonian,sub_self,mul_zero,Finset.sum_const_zero,sub_zero,zero_add] using!
    (covariant.add_const sourcePotential).add (plateau_energy_derivative t)

theorem plateau_junctions (r momentum : Configuration) :
    plateauHamiltonian 0 r momentum=rampHamiltonian initialMomentum 0 0 r momentum ∧
    plateauHamiltonian duration r momentum=rampHamiltonian (plateauMomentum 1) 0 0 r momentum := by
  have force0 : plateauForce 0=0 := by funext i; simp [plateauForce,progress_rate_endpoints.1]
  have force1 : plateauForce duration=0 := by funext i; simp [plateauForce,progress_rate_endpoints.2]
  have p0 : plateauMomentum 0=initialMomentum := by funext i; simp [plateauMomentum]
  rw [ramp_control_held,ramp_control_held]
  simp [plateauHamiltonian,progress_endpoints.1,progress_endpoints.2,force0,force1,p0]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation
