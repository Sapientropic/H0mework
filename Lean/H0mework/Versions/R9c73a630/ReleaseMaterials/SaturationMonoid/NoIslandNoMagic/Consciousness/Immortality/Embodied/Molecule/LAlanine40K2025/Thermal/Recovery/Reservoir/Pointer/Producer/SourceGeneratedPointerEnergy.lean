import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Producer.SourceGeneratedPointerCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerControlWork

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Live

open Collision Propagation.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Pointer.baselineHamiltonian Pointer.loadPulse

def baselineEnergy (current : State) : ℝ := energy Pointer.baselineHamiltonian current.joint
def controlEnergy (current : State) : ℝ := energy sourceHamiltonian current.joint
def switchInWork (current : State) : ℝ := controlEnergy current - baselineEnergy current
def switchOutWork (current : State) : ℝ := baselineEnergy current - controlEnergy current
def measurementWork (current : State) : ℝ := switchInWork current + switchOutWork (measureNext current)

theorem measureNext_preserves_control (current : State) :
    controlEnergy (measureNext current) = controlEnergy current := by
  rw [controlEnergy, measureNext_joint]
  exact sourceControl_conserves current.joint

theorem measurementWork_actual (current : State) :
    measurementWork current = baselineEnergy (measureNext current) - baselineEnergy current := by
  unfold measurementWork switchInWork switchOutWork
  rw [measureNext_preserves_control]
  ring

theorem loadNext_preserves_baseline (current : State) :
    baselineEnergy (loadNext current) = baselineEnergy current := by
  have commutes := matrix_generator_commutes Pointer.baselineHamiltonian (nativeClockStep : ℝ)
  rw [← Pointer.loadPulse_baseline] at commutes
  unfold baselineEnergy
  rw [loadNext_joint]
  simpa only [Quantum.conjugation_apply] using
    Recovery.PreparationEnergy.commuting_energy Pointer.baselineHamiltonian current.joint
      (Pointer.loadPulse (nativeClockStep : ℝ)) commutes

theorem baselineEnergy_split (current : State) :
    baselineEnergy current = energy Physical.baselineHamiltonian (bodyRead current.joint) +
      pointerEnergy current.joint := by
  unfold baselineEnergy Pointer.baselineHamiltonian pointerEnergy
  exact block_energy_split Physical.baselineHamiltonian 2 current.joint

theorem measurementWork_body_pointer (current : State) :
    measurementWork current =
      (energy Physical.baselineHamiltonian (bodyRead (measureNext current).joint) -
        energy Physical.baselineHamiltonian (bodyRead current.joint)) +
      (pointerEnergy (measureNext current).joint - pointerEnergy current.joint) := by
  rw [measurementWork_actual, baselineEnergy_split, baselineEnergy_split]
  ring

theorem loadNext_pointer_energy (current : State) :
    pointerEnergy (loadNext current).joint = pointerEnergy current.joint := by
  rw [pointerEnergy, loadNext_pointer_one]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Live
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
