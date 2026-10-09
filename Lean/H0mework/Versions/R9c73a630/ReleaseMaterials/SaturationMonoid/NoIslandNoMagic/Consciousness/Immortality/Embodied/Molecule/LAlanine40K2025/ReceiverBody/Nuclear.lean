import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime.Consumers
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNuclearKinetic
set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody
open Force.Interface Inertia.SourceParsing
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

def stock : ℝ := Extract.Port.kinetic
  (ControlRecovery.Runtime.readCurrent ControlRecovery.Runtime.afterSecond).momentum

theorem stock_positive : (2/25 : ℝ) < stock :=
  ControlRecovery.Runtime.actual_receiver_positive ControlRecovery.Runtime.afterFirst

theorem reported_kinetic_bounds :
    (1 : ℚ)/10^24 < Reentry.Source.stepReadout.nuclear.target.kinetic ∧
      Reentry.Source.stepReadout.nuclear.target.kinetic < (1 : ℚ)/50 := by
  change (1 : ℚ)/10^24 < rationalRead _ ∧ rationalRead _ < (1 : ℚ)/50
  norm_num [rationalRead]

theorem exact_kinetic_budget :
    0 < Reentry.Producer.targetMomentumKinetic ∧
      3*Reentry.Producer.targetMomentumKinetic < (2/25 : ℚ) := by
  have error := Reentry.Producer.targetKineticResidual_bound
  unfold Reentry.Producer.targetKineticResidual at error
  have lower := (abs_lt.mp error).1
  have upper := (abs_lt.mp error).2
  constructor <;> linarith only [lower,upper,reported_kinetic_bounds.1,reported_kinetic_bounds.2]

def boostedMomentum (atom : Atom) (axis : Axis) : ℚ :=
  2*Reentry.Source.stepReadout.nuclear.target.momentum atom axis

def boostedKinetic : ℚ := ∑ atom : Atom, (∑ axis : Axis, boostedMomentum atom axis^2)/
  (2*Reentry.Source.stepReadout.nuclear.masses atom)

theorem boosted_kinetic_exact : boostedKinetic=4*Reentry.Producer.targetMomentumKinetic := by
  unfold boostedKinetic Reentry.Producer.targetMomentumKinetic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro atom _
  have inner : (∑ axis : Axis, boostedMomentum atom axis^2)=
      4*∑ axis : Axis, Reentry.Source.stepReadout.nuclear.target.momentum atom axis^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro axis _
    unfold boostedMomentum
    ring
  rw [inner]
  ring

theorem boost_cost_positive_and_below_stock :
    0 < (boostedKinetic-Reentry.Producer.targetMomentumKinetic : ℚ) ∧
      ((boostedKinetic-Reentry.Producer.targetMomentumKinetic : ℚ) : ℝ) < stock := by
  rw [boosted_kinetic_exact]
  constructor
  · linarith only [exact_kinetic_budget.1]
  · have budget : ((4*Reentry.Producer.targetMomentumKinetic-Reentry.Producer.targetMomentumKinetic : ℚ) : ℝ) < (2/25 : ℝ) := by
      have rational : 4*Reentry.Producer.targetMomentumKinetic-Reentry.Producer.targetMomentumKinetic < (2/25 : ℚ) := by
        linarith only [exact_kinetic_budget.2]
      have casted : ((4*Reentry.Producer.targetMomentumKinetic-Reentry.Producer.targetMomentumKinetic : ℚ) : ℝ) < ((2/25 : ℚ) : ℝ) :=
        Rat.cast_lt.mpr rational
      norm_num only [Rat.cast_div,Rat.cast_ofNat] at casted
      exact casted
    exact budget.trans stock_positive

theorem boosted_momentum_changed : boostedMomentum ≠ Reentry.Source.stepReadout.nuclear.target.momentum := by
  intro same
  have kinetic : boostedKinetic=Reentry.Producer.targetMomentumKinetic := by
    unfold boostedKinetic
    rw [same]
    rfl
  have positive := boost_cost_positive_and_below_stock.1
  rw [kinetic,sub_self] at positive
  exact (lt_irrefl 0) positive

theorem held_potential_energy_account :
    boostedKinetic+Reentry.Source.stepReadout.nuclear.target.potential-Reentry.Source.stepReadout.nuclear.target.total=
      3*Reentry.Producer.targetMomentumKinetic-Reentry.Producer.targetKineticResidual := by
  rw [boosted_kinetic_exact,Reentry.Producer.targetMechanicalEnergyWholeAccount]
  ring

abbrev Coordinate := Atom × Axis
abbrev Configuration := Coordinate → ℝ

def sourcePosition (i : Coordinate) : ℝ := Reentry.Source.stepReadout.nuclear.target.position i.1 i.2
def sourceMomentum (i : Coordinate) : ℝ := Reentry.Source.stepReadout.nuclear.target.momentum i.1 i.2
def duration : ℝ := Propagation.Producer.nativeClockStep
def controlForce (i : Coordinate) : ℝ := sourceMomentum i/duration
def controlHamiltonian (position : Configuration) (_momentum : Configuration) : ℝ :=
  -∑ i, controlForce i*position i
def positionPath (_time : ℝ) : Configuration := sourcePosition
def momentumPath (time : ℝ) (i : Coordinate) : ℝ := sourceMomentum i+time*controlForce i

theorem momentum_path_derivative (time : ℝ) (i : Coordinate) :
    HasDerivAt (fun t => momentumPath t i) (controlForce i) time := by
  simpa only [momentumPath,id_eq,one_mul] using!
    (((hasDerivAt_id time).mul_const (controlForce i)).const_add (sourceMomentum i))

theorem position_path_derivative (time : ℝ) (i : Coordinate) :
    HasDerivAt (fun t => positionPath t i) 0 time := hasDerivAt_const time _

theorem momentum_endpoint (i : Coordinate) :
    momentumPath duration i=(boostedMomentum i.1 i.2 : ℝ) := by
  have positive : 0 < duration := by
    change 0 < (Propagation.Producer.nativeClockStep : ℝ)
    exact_mod_cast Propagation.Producer.nativeClockStep_positive
  have cancel : duration*(sourceMomentum i/duration)=sourceMomentum i := by field_simp
  rw [momentumPath,controlForce,cancel]
  simp only [boostedMomentum,Rat.cast_mul,Rat.cast_ofNat,sourceMomentum]
  ring

theorem control_position_derivative (position momentum : Configuration) (i : Coordinate) (time : ℝ) :
    HasDerivAt (fun t => controlHamiltonian (Function.update position i (position i+t)) momentum)
      (-controlForce i) time := by
  have value (t : ℝ) : controlHamiltonian (Function.update position i (position i+t)) momentum=
      controlHamiltonian position momentum-t*controlForce i := by
    unfold controlHamiltonian
    have updated : ∑ j, controlForce j*(Function.update position i (position i+t)) j=
        (∑ j, controlForce j*position j)+controlForce i*t := by
      have entry (j : Coordinate) : controlForce j*(Function.update position i (position i+t)) j=
          controlForce j*position j+(if j=i then controlForce i*t else 0) := by
        by_cases same : j=i
        · subst j; simp; ring
        · simp [same]
      simp_rw [entry,Finset.sum_add_distrib]
      simp
    rw [updated]
    ring
  simp_rw [value]
  simpa only [id_eq,one_mul,Pi.sub_apply,zero_sub] using!
    ((hasDerivAt_const time (controlHamiltonian position momentum)).sub
      ((hasDerivAt_id time).mul_const (controlForce i)))

theorem control_momentum_derivative (position momentum : Configuration) (i : Coordinate) (time : ℝ) :
    HasDerivAt (fun t => controlHamiltonian position (Function.update momentum i (momentum i+t))) 0 time :=
  hasDerivAt_const time _

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody
