import H0mework.Chemistry.LAlanineWork.GeneratedFieldCycle
import H0mework.Chemistry.LAlanineWork.UnitaryWorkCapacity

/-! # The field cycle's target work capacity is computed, not assumed -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Drive

open Capacity Collision Quantum Unitary
open Propagation.Interface Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped ComplexOrder

noncomputable section

def fieldBaseline : JointMatrix Basis := pairH energyHamiltonian pairCoupling

theorem fieldBaseline_hermitian : fieldBaseline.IsHermitian :=
  pairH_hermitian energyHamiltonian energyHamiltonian_hermitian pairCoupling

def fieldCycleUnitary : Matrix.unitaryGroup (Basis × Basis) ℂ :=
  pairUnitary fieldOffHamiltonian fieldOffHamiltonian_hermitian pairCoupling (nativeClockStep : ℝ)

theorem fieldCycleAdvance_eq_conjugation (current : JointMatrix Basis) :
    fieldCycleAdvance current = conjStarAlgAut ℂ _ fieldCycleUnitary current := by
  dsimp only [fieldCycleAdvance, fieldCycleUnitary]
  rw [conjStarAlgAut_apply]
  exact pairAdvance_eq_unitary fieldOffHamiltonian fieldOffHamiltonian_hermitian pairCoupling _ current

theorem fieldCycleAdvance_hermitian (current : JointMatrix Basis) (hermitian : current.IsHermitian) :
    (fieldCycleAdvance current).IsHermitian := by
  rw [fieldCycleAdvance_eq_conjugation]
  exact conjugatedHermitian current hermitian fieldCycleUnitary

def fieldCapacity (current : JointMatrix Basis) (hermitian : current.IsHermitian) : ℝ :=
  ergotropy fieldBaseline current fieldBaseline_hermitian hermitian

theorem fieldCapacity_nonnegative (current : JointMatrix Basis) (hermitian : current.IsHermitian) :
    0 ≤ fieldCapacity current hermitian := ergotropy_nonnegative _ _ _ _

/-- The work from the two switching events pays exactly for the changed optimal extractable work. -/
theorem fieldCycle_capacityBalance (current : JointMatrix Basis) (hermitian : current.IsHermitian) :
    fieldCapacity (fieldCycleAdvance current) (fieldCycleAdvance_hermitian current hermitian) -
      fieldCapacity current hermitian = fieldCycleWork current := by
  rw [fieldCycle_workBalance]
  unfold fieldCapacity
  have same := passiveEnergy_eq_of_charpoly fieldBaseline (fieldCycleAdvance current) current
    fieldBaseline_hermitian (fieldCycleAdvance_hermitian current hermitian) hermitian (by
      rw [fieldCycleAdvance_eq_conjugation]
      exact conjugated_charpoly current fieldCycleUnitary)
  unfold ergotropy
  rw [same]
  dsimp only [fieldBaseline]
  ring

theorem sourceFieldCycle_capacityBalance :
    fieldCapacity sourceFieldCycleTarget sourceFieldCycleTarget_positive_normalized.1.isHermitian -
      fieldCapacity sourceFieldCycleCurrent sourceFieldCycleCurrent_positive_normalized.1.isHermitian =
      fieldCycleWork sourceFieldCycleCurrent :=
  fieldCycle_capacityBalance sourceFieldCycleCurrent sourceFieldCycleCurrent_positive_normalized.1.isHermitian

theorem sourceFieldCycle_targetCapacity_attained :
    energy fieldBaseline sourceFieldCycleTarget -
      energy fieldBaseline (conjStarAlgAut ℂ _
        (passiveUnitary fieldBaseline sourceFieldCycleTarget fieldBaseline_hermitian
          sourceFieldCycleTarget_positive_normalized.1.isHermitian) sourceFieldCycleTarget) =
      fieldCapacity sourceFieldCycleTarget sourceFieldCycleTarget_positive_normalized.1.isHermitian :=
  ergotropy_attained _ _ _ _

end

end LAlanine40K2025.Thermal.Work.Drive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
