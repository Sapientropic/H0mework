import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Nuclear

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody
open Force.Interface
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

def mass (i : Coordinate) : ℝ := Reentry.Source.stepReadout.nuclear.masses i.1
def sourceForce (i : Coordinate) : ℝ := Reentry.Source.stepReadout.nuclear.target.force i.1 i.2
def sourcePotential : ℝ := Reentry.Source.stepReadout.nuclear.target.potential
def nuclearKinetic (momentum : Configuration) : ℝ := ∑ i, momentum i^2/(2*mass i)

theorem mass_positive (i : Coordinate) : 0 < mass i := by
  unfold mass
  exact_mod_cast Inertia.Producer.masses_positive i.1

theorem nuclear_kinetic_source : nuclearKinetic sourceMomentum=(Reentry.Producer.targetMomentumKinetic : ℝ) := by
  simp only [nuclearKinetic,Fintype.sum_prod_type,sourceMomentum,mass,
    Reentry.Producer.targetMomentumKinetic,Rat.cast_sum,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_ofNat,
    Finset.sum_div]

theorem nuclear_kinetic_target : nuclearKinetic (momentumPath duration)=(boostedKinetic : ℝ) := by
  simp only [nuclearKinetic,Fintype.sum_prod_type,momentum_endpoint,mass,boostedKinetic,
    Rat.cast_sum,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_ofNat,Finset.sum_div]

-- This is the original force jet at the held M3 configuration.
def sourcePotentialGerm (position : Configuration) : ℝ :=
  sourcePotential-∑ i, sourceForce i*(position i-sourcePosition i)

def drivePotential (position : Configuration) : ℝ :=
  -∑ i, (controlForce i-sourceForce i)*(position i-sourcePosition i)

-- The canonical momentum equals A on the plateau; mechanical momentum is p - A.
def covariantKinetic (clock : ℝ) (momentum : Configuration) : ℝ :=
  nuclearKinetic (momentum-momentumPath clock)

def bodyHamiltonian (clock : ℝ) (position momentum : Configuration) : ℝ :=
  covariantKinetic clock momentum+sourcePotentialGerm position+drivePotential position

def baselineHamiltonian (position momentum : Configuration) : ℝ :=
  nuclearKinetic momentum+sourcePotentialGerm position

theorem total_potential (position : Configuration) :
    sourcePotentialGerm position+drivePotential position=
      sourcePotential+controlHamiltonian (position-sourcePosition) sourceMomentum := by
  simp only [sourcePotentialGerm,drivePotential,controlHamiltonian,Pi.sub_apply,
    sub_mul,Finset.sum_sub_distrib]
  ring

theorem body_hamiltonian_exact (clock : ℝ) (position momentum : Configuration) :
    bodyHamiltonian clock position momentum=
      covariantKinetic clock momentum+sourcePotential+controlHamiltonian (position-sourcePosition) sourceMomentum := by
  rw [bodyHamiltonian,add_assoc,total_potential]
  ring

theorem potential_at_source : sourcePotentialGerm sourcePosition=sourcePotential := by
  simp [sourcePotentialGerm]

theorem body_energy_on_path (clock : ℝ) :
    bodyHamiltonian clock (positionPath clock) (momentumPath clock)=sourcePotential := by
  simp [bodyHamiltonian,covariantKinetic,nuclearKinetic,positionPath,
    sourcePotentialGerm,drivePotential]

theorem body_position_derivative (clock : ℝ) (position momentum : Configuration) (i : Coordinate) :
    HasDerivAt (fun h => bodyHamiltonian clock (Function.update position i (position i+h)) momentum)
      (-controlForce i) 0 := by
  have shifted (h : ℝ) : Function.update position i (position i+h)-sourcePosition=
      Function.update (position-sourcePosition) i ((position-sourcePosition) i+h) := by
    funext j
    by_cases same : j=i
    · subst j; simp; ring
    · simp [same]
  simp_rw [body_hamiltonian_exact,shifted]
  exact (control_position_derivative (position-sourcePosition) sourceMomentum i 0).const_add _

theorem covariant_momentum_derivative (clock : ℝ) (momentum : Configuration) (i : Coordinate) :
    HasDerivAt (fun h => covariantKinetic clock (Function.update momentum i (momentum i+h)))
      ((momentum i-momentumPath clock i)/mass i) 0 := by
  have value (h : ℝ) : covariantKinetic clock (Function.update momentum i (momentum i+h))=
      covariantKinetic clock momentum+
        ((momentum i+h-momentumPath clock i)^2-(momentum i-momentumPath clock i)^2)/(2*mass i) := by
    unfold covariantKinetic nuclearKinetic
    have entry (j : Coordinate) :
        (Function.update momentum i (momentum i+h)-momentumPath clock) j^2/(2*mass j)=
          (momentum-momentumPath clock) j^2/(2*mass j)+
            if j=i then ((momentum i+h-momentumPath clock i)^2-(momentum i-momentumPath clock i)^2)/(2*mass i) else 0 := by
      by_cases same : j=i
      · subst j; simp; ring
      · simp [same]
    simp_rw [entry,Finset.sum_add_distrib]
    simp
  simp_rw [value]
  have derivative : HasDerivAt (fun h : ℝ => covariantKinetic clock momentum+
      ((momentum i+h-momentumPath clock i)^2-(momentum i-momentumPath clock i)^2)/(2*mass i))
      (2*(momentum i-momentumPath clock i)/(2*mass i)) 0 := by
    simpa using! ((((((hasDerivAt_id (0 : ℝ)).const_add (momentum i)).sub_const (momentumPath clock i)).pow 2).sub_const
      ((momentum i-momentumPath clock i)^2)).div_const (2*mass i)).const_add (covariantKinetic clock momentum)
  convert derivative using 1
  ring

theorem body_momentum_derivative_on_path (clock : ℝ) (i : Coordinate) :
    HasDerivAt (fun h => bodyHamiltonian clock (positionPath clock)
      (Function.update (momentumPath clock) i (momentumPath clock i+h))) 0 0 := by
  simpa only [bodyHamiltonian,sub_self,zero_div] using
    ((covariant_momentum_derivative clock (momentumPath clock) i).add_const
      (sourcePotentialGerm (positionPath clock))).add_const (drivePotential (positionPath clock))

theorem covariant_clock_derivative (clock : ℝ) (momentum : Configuration) :
    HasDerivAt (fun t => covariantKinetic t momentum)
      (∑ i, -(momentum i-momentumPath clock i)*controlForce i/mass i) clock := by
  have entry (i : Coordinate) :
      HasDerivAt (fun t => (momentum i-momentumPath t i)^2/(2*mass i))
        (-(momentum i-momentumPath clock i)*controlForce i/mass i) clock := by
    have derivative : HasDerivAt (fun t => (momentum i-momentumPath t i)^2/(2*mass i))
        (2*(momentum i-momentumPath clock i)*(-controlForce i)/(2*mass i)) clock := by
      simpa using! ((((hasDerivAt_const clock (momentum i)).sub (momentum_path_derivative clock i)).pow 2).div_const (2*mass i))
    convert derivative using 1
    ring
  simpa only [covariantKinetic,nuclearKinetic,Pi.sub_apply] using!
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => entry i))

theorem body_clock_derivative_on_path (clock : ℝ) :
    HasDerivAt (fun t => bodyHamiltonian t (positionPath clock) (momentumPath clock)) 0 clock := by
  simpa only [bodyHamiltonian,sub_self,neg_zero,zero_mul,zero_div,Finset.sum_const_zero] using
    ((covariant_clock_derivative clock (momentumPath clock)).add_const
      (sourcePotentialGerm (positionPath clock))).add_const (drivePotential (positionPath clock))

def receiverInitial : ℝ :=
  (ControlRecovery.Runtime.readCurrent ControlRecovery.Runtime.afterSecond).momentum

theorem receiver_initial_positive : (2/25 : ℝ) < receiverInitial := by
  change (2/25 : ℝ) < (ControlRecovery.Runtime.readCurrent ControlRecovery.Runtime.afterFirst.tick.next).momentum
  rw [ControlRecovery.Runtime.actual_receiver_stored ControlRecovery.Runtime.afterFirst]
  exact ControlRecovery.Receiver.output_momentum

theorem stock_eq_initial : stock=receiverInitial :=
  abs_of_pos (lt_trans (by norm_num) receiver_initial_positive)

-- The switch coordinate has the same impulsive meaning as Extract.Port.
def switchPotential (old new coordinate : ℝ) : ℝ := old+coordinate*(new-old)
def switchForce (old new : ℝ) : ℝ := -(new-old)
def switchMomentum (old new initial coordinate : ℝ) : ℝ := initial+coordinate*switchForce old new

theorem switch_potential_derivative (old new coordinate : ℝ) :
    HasDerivAt (switchPotential old new) (-switchForce old new) coordinate := by
  simpa only [switchPotential,switchForce,neg_neg,id_eq,one_mul] using!
    ((hasDerivAt_id coordinate).mul_const (new-old)).const_add old

theorem switch_momentum_derivative (old new initial coordinate : ℝ) :
    HasDerivAt (switchMomentum old new initial) (switchForce old new) coordinate := by
  simpa only [switchMomentum,id_eq,one_mul] using!
    ((hasDerivAt_id coordinate).mul_const (switchForce old new)).const_add initial

theorem switch_integral (old new initial : ℝ) :
    switchMomentum old new initial 1-initial=∫ _x in (0 : ℝ)..1, switchForce old new := by
  simp [switchMomentum]

theorem switch_balance (old new initial coordinate : ℝ) :
    switchPotential old new coordinate+switchMomentum old new initial coordinate=old+initial := by
  unfold switchPotential switchMomentum switchForce
  ring

def onPath (coordinate : ℝ) : ℝ :=
  switchMomentum (baselineHamiltonian sourcePosition sourceMomentum)
    (bodyHamiltonian 0 sourcePosition sourceMomentum) receiverInitial coordinate
def offPath (coordinate : ℝ) : ℝ :=
  switchMomentum (bodyHamiltonian duration (positionPath duration) (momentumPath duration))
    (baselineHamiltonian (positionPath duration) (momentumPath duration)) (onPath 1) coordinate
def receiverTarget : ℝ := offPath 1

theorem on_source_energy : bodyHamiltonian 0 sourcePosition sourceMomentum=sourcePotential := by
  have initial : momentumPath 0=sourceMomentum := by funext i; simp [momentumPath]
  simpa only [positionPath,initial] using body_energy_on_path 0

theorem on_path_exact (coordinate : ℝ) :
    onPath coordinate=receiverInitial+coordinate*(Reentry.Producer.targetMomentumKinetic : ℝ) := by
  rw [onPath,switchMomentum,switchForce,on_source_energy,baselineHamiltonian,potential_at_source,nuclear_kinetic_source]
  ring

theorem off_path_exact (coordinate : ℝ) :
    offPath coordinate=onPath 1-coordinate*(boostedKinetic : ℝ) := by
  rw [offPath,switchMomentum,switchForce,body_energy_on_path,baselineHamiltonian,
    nuclear_kinetic_target,positionPath,potential_at_source]
  ring

theorem receiver_target_debit : receiverInitial-receiverTarget=
    ((boostedKinetic-Reentry.Producer.targetMomentumKinetic : ℚ) : ℝ) := by
  rw [receiverTarget,off_path_exact,on_path_exact]
  push_cast
  ring

theorem receiver_target_positive : 0 < receiverTarget := by
  have paid := boost_cost_positive_and_below_stock.2
  rw [stock_eq_initial] at paid
  linarith only [paid,receiver_target_debit]

theorem on_path_positive (coordinate : ℝ) (lo : 0 ≤ coordinate) : 0 < onPath coordinate := by
  rw [on_path_exact]
  have k : 0 ≤ (Reentry.Producer.targetMomentumKinetic : ℝ) := Rat.cast_nonneg.mpr exact_kinetic_budget.1.le
  exact add_pos_of_pos_of_nonneg (lt_trans (by norm_num) receiver_initial_positive) (mul_nonneg lo k)

theorem off_path_positive (coordinate : ℝ) (lo : 0 ≤ coordinate) (hi : coordinate ≤ 1) :
    0 < offPath coordinate := by
  have linear : offPath coordinate=(1-coordinate)*onPath 1+coordinate*receiverTarget := by
    rw [off_path_exact,receiverTarget,off_path_exact]
    ring
  have start := on_path_positive 1 (by norm_num)
  have finish := receiver_target_positive
  rw [linear]
  nlinarith [mul_nonneg (sub_nonneg.mpr hi) start.le,mul_nonneg lo finish.le]

theorem body_receiver_energy_account :
    baselineHamiltonian (positionPath duration) (momentumPath duration)+Extract.Port.kinetic receiverTarget=
      baselineHamiltonian sourcePosition sourceMomentum+Extract.Port.kinetic receiverInitial := by
  rw [baselineHamiltonian,baselineHamiltonian,positionPath,potential_at_source,
    nuclear_kinetic_source,nuclear_kinetic_target,Extract.Port.kinetic,Extract.Port.kinetic,
    abs_of_pos receiver_target_positive,abs_of_pos (lt_trans (by norm_num) receiver_initial_positive)]
  have debit := receiver_target_debit
  push_cast at debit
  linarith only [debit]

theorem original_recorded_energy_account :
    (boostedKinetic : ℝ)+sourcePotential+Extract.Port.kinetic receiverTarget-
      ((Reentry.Source.stepReadout.nuclear.target.total : ℝ)+Extract.Port.kinetic receiverInitial)=
        -(Reentry.Producer.targetKineticResidual : ℝ) := by
  have account := body_receiver_energy_account
  simp only [baselineHamiltonian,positionPath,potential_at_source,nuclear_kinetic_source,nuclear_kinetic_target] at account
  have original := congrArg (fun x : ℚ => (x : ℝ)) Reentry.Producer.targetMechanicalEnergyWholeAccount
  push_cast at original
  change (Reentry.Source.stepReadout.nuclear.target.total : ℝ)=
    (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential+(Reentry.Producer.targetKineticResidual : ℝ) at original
  linarith only [account,original]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody
