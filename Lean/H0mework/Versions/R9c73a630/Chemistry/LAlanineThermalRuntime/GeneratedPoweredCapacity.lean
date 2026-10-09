import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalRuntime.GeneratedPoweredCurrent

/-! # Actual reduced spectra, remaining controller capacity, and the inclusive work budget -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Producer

open Propagation.Interface Propagation.Producer Work.Capacity
open scoped ComplexOrder

noncomputable section

def poweredPair (current : PoweredState) : Collision.JointMatrix Basis := Dynamics.systemReduce current.joint

def poweredController (current : PoweredState) : Matrix (Fin 2) (Fin 2) ℂ := Dynamics.controllerReduce current.joint

theorem poweredPair_positive (current : PoweredState) : (poweredPair current).PosSemidef :=
  Dynamics.systemReduce_posSemidef current.joint current.positive

theorem poweredController_positive (current : PoweredState) : (poweredController current).PosSemidef :=
  Dynamics.controllerReduce_posSemidef current.joint current.positive

def poweredPairCapacity (current : PoweredState) : ℝ :=
  Work.Drive.fieldCapacity (poweredPair current) (poweredPair_positive current).isHermitian

def poweredPairPassiveEnergy (current : PoweredState) : ℝ :=
  passiveEnergy Work.Drive.fieldBaseline (poweredPair current) Work.Drive.fieldBaseline_hermitian
    (poweredPair_positive current).isHermitian

def poweredControllerCapacity (current : PoweredState) : ℝ :=
  ergotropy (Dynamics.controllerHamiltonian 2) (poweredController current)
    (Dynamics.controllerHamiltonian_hermitian 2) (poweredController_positive current).isHermitian

def poweredControllerPassiveEnergy (current : PoweredState) : ℝ :=
  passiveEnergy (Dynamics.controllerHamiltonian 2) (poweredController current)
    (Dynamics.controllerHamiltonian_hermitian 2) (poweredController_positive current).isHermitian

theorem poweredCapacities_nonnegative (current : PoweredState) :
    0 ≤ poweredPairCapacity current ∧ 0 ≤ poweredControllerCapacity current :=
  ⟨ergotropy_nonnegative _ _ _ _, ergotropy_nonnegative _ _ _ _⟩

/-- The output pair is not a unitary image of its previous marginal; its passive energy is recomputed. -/
theorem poweredPair_capacityBalance (current : PoweredState) :
    poweredPairCapacity (poweredStateNext current) - poweredPairCapacity current =
      poweredPairEnergy (poweredStateNext current) - poweredPairEnergy current -
        (poweredPairPassiveEnergy (poweredStateNext current) - poweredPairPassiveEnergy current) := by
  unfold poweredPairCapacity Work.Drive.fieldCapacity ergotropy poweredPairPassiveEnergy
    poweredPairEnergy Dynamics.systemEnergy poweredPair
  ring

theorem poweredLocal_capacityBalance (current : PoweredState) :
    (poweredPairCapacity (poweredStateNext current) - poweredPairCapacity current) +
      (poweredControllerCapacity (poweredStateNext current) - poweredControllerCapacity current) +
      (poweredPairPassiveEnergy (poweredStateNext current) - poweredPairPassiveEnergy current) +
      (poweredControllerPassiveEnergy (poweredStateNext current) - poweredControllerPassiveEnergy current) = 0 := by
  have balance := poweredStateNext_energyBalance current
  unfold poweredPairCapacity Work.Drive.fieldCapacity poweredControllerCapacity ergotropy
    poweredPairPassiveEnergy poweredControllerPassiveEnergy poweredPair poweredController
  unfold poweredPairEnergy poweredControllerEnergy Dynamics.systemEnergy Dynamics.controllerEnergy at balance
  linarith

def poweredTotalHamiltonian : Dynamics.ControllerJoint (Basis × Basis) :=
  Dynamics.totalHamiltonian Work.Drive.fieldBaseline 2 Source.sourceInteraction

theorem poweredTotalHamiltonian_hermitian : poweredTotalHamiltonian.IsHermitian :=
  Dynamics.totalHamiltonian_hermitian _ _ _ Work.Drive.fieldBaseline_hermitian Source.sourceInteraction_hermitian

def poweredJointCapacity (current : PoweredState) : ℝ :=
  ergotropy poweredTotalHamiltonian current.joint poweredTotalHamiltonian_hermitian current.positive.isHermitian

theorem poweredJoint_capacityConserved (current : PoweredState) :
    poweredJointCapacity (poweredStateNext current) = poweredJointCapacity current := by
  have changeCapacity := ergotropy_unitary_change poweredTotalHamiltonian current.joint
    poweredTotalHamiltonian_hermitian current.positive.isHermitian
    (Dynamics.flowUnitary Work.Drive.fieldBaseline 2 Source.sourceInteraction
      Work.Drive.fieldBaseline_hermitian Source.sourceInteraction_hermitian (nativeClockStep : ℝ))
  have energyConserved := Dynamics.totalEnergy_conserved Work.Drive.fieldBaseline 2 Source.sourceInteraction
    Work.Drive.fieldBaseline_hermitian Source.sourceInteraction_hermitian (nativeClockStep : ℝ) current.joint
  change poweredJointCapacity (poweredStateNext current) - poweredJointCapacity current =
    Collision.energy poweredTotalHamiltonian (poweredStateNext current).joint -
      Collision.energy poweredTotalHamiltonian current.joint at changeCapacity
  change Collision.energy poweredTotalHamiltonian (poweredStateNext current).joint =
    Collision.energy poweredTotalHamiltonian current.joint at energyConserved
  rw [energyConserved, sub_self] at changeCapacity
  exact sub_eq_zero.mp changeCapacity

theorem poweredPair_capacityAttained (current : PoweredState) :
    Collision.energy Work.Drive.fieldBaseline (poweredPair current) -
      Collision.energy Work.Drive.fieldBaseline (Unitary.conjStarAlgAut ℂ _
        (passiveUnitary Work.Drive.fieldBaseline (poweredPair current) Work.Drive.fieldBaseline_hermitian
          (poweredPair_positive current).isHermitian) (poweredPair current)) = poweredPairCapacity current :=
  ergotropy_attained _ _ _ _

theorem poweredController_capacityAttained (current : PoweredState) :
    Collision.energy (Dynamics.controllerHamiltonian 2) (poweredController current) -
      Collision.energy (Dynamics.controllerHamiltonian 2) (Unitary.conjStarAlgAut ℂ _
        (passiveUnitary (Dynamics.controllerHamiltonian 2) (poweredController current)
          (Dynamics.controllerHamiltonian_hermitian 2) (poweredController_positive current).isHermitian)
        (poweredController current)) = poweredControllerCapacity current :=
  ergotropy_attained _ _ _ _

end

end LAlanine40K2025.Thermal.Powered.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
