import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedRememberedPair

/-!
# Source-owned removal and restoration of the already installed field

The registered control switches Hactive to the same source's H0, evolves for q,
then restores Hactive. The two ideal switching events are work channels, not heat
or a bath reset. No new field amplitude, duration, trajectory or target is input.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Drive

open Propagation.Interface Propagation.Producer Preparation Collision Quantum
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Producer
open scoped ComplexOrder Matrix

noncomputable section

def fieldOffSource : ElectronicPropagationSource := { electronicSource with zQ := fun _ => 0 }

def fieldOffHamiltonian : SystemMatrix Basis := energyCoordinates (activeMatrix fieldOffSource)

theorem fieldOffHamiltonian_hermitian : fieldOffHamiltonian.IsHermitian := by
  change (energyCoordinates (activeMatrix fieldOffSource))ᴴ = energyCoordinates (activeMatrix fieldOffSource)
  unfold energyCoordinates
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, (activeMatrix_hermitian fieldOffSource).eq, Matrix.mul_assoc]

def fieldCycleAdvance (current : JointMatrix Basis) : JointMatrix Basis :=
  pairAdvance fieldOffHamiltonian pairCoupling (nativeClockStep : ℝ) current

def fieldCycleOffWork (current : JointMatrix Basis) : ℝ :=
  energy (pairH fieldOffHamiltonian pairCoupling) current -
    energy (pairH energyHamiltonian pairCoupling) current

def fieldCycleOnWork (current : JointMatrix Basis) : ℝ :=
  energy (pairH energyHamiltonian pairCoupling) (fieldCycleAdvance current) -
    energy (pairH fieldOffHamiltonian pairCoupling) (fieldCycleAdvance current)

def fieldCycleWork (current : JointMatrix Basis) : ℝ :=
  fieldCycleOffWork current + fieldCycleOnWork current

theorem fieldCycleAdvance_posSemidef (current : JointMatrix Basis) (positive : current.PosSemidef) :
    (fieldCycleAdvance current).PosSemidef :=
  pairAdvance_posSemidef fieldOffHamiltonian fieldOffHamiltonian_hermitian pairCoupling _ current positive

theorem fieldCycleAdvance_trace (current : JointMatrix Basis) :
    (fieldCycleAdvance current).trace = current.trace :=
  pairAdvance_trace fieldOffHamiltonian fieldOffHamiltonian_hermitian pairCoupling _ current

/-- The dwell conserves its actual H0-pair energy, not the baseline Hactive energy. -/
theorem fieldCycle_dwellEnergy (current : JointMatrix Basis) :
    energy (pairH fieldOffHamiltonian pairCoupling) (fieldCycleAdvance current) =
      energy (pairH fieldOffHamiltonian pairCoupling) current :=
  congrArg Complex.re (pairAdvance_totalEnergy fieldOffHamiltonian fieldOffHamiltonian_hermitian
    pairCoupling _ current)

theorem fieldCycle_workBalance (current : JointMatrix Basis) :
    fieldCycleWork current =
      energy (pairH energyHamiltonian pairCoupling) (fieldCycleAdvance current) -
        energy (pairH energyHamiltonian pairCoupling) current := by
  unfold fieldCycleWork fieldCycleOffWork fieldCycleOnWork
  rw [fieldCycle_dwellEnergy]
  ring

theorem fieldCycle_interactionEnergy (current : JointMatrix Basis) :
    energy ((pairCoupling : ℂ) • swapOperator) (fieldCycleAdvance current) =
      energy ((pairCoupling : ℂ) • swapOperator) current :=
  congrArg Complex.re (pairAdvance_interactionEnergy fieldOffHamiltonian fieldOffHamiltonian_hermitian
    pairCoupling _ current)

theorem fieldCycle_spectralEntropy (current : JointMatrix Basis) (positive : current.PosSemidef)
    (normalized : current.trace = 1) :
    spectralEntropy (fieldCycleAdvance current) (fieldCycleAdvance_posSemidef current positive)
      ((fieldCycleAdvance_trace current).trans normalized) = spectralEntropy current positive normalized :=
  pairAdvance_spectralEntropy fieldOffHamiltonian fieldOffHamiltonian_hermitian pairCoupling _
    current positive normalized

def sourceFieldCycleCurrent : JointMatrix Basis := rememberedJoint (nativeClockStep : ℝ)
def sourceFieldCycleTarget : JointMatrix Basis := fieldCycleAdvance sourceFieldCycleCurrent

theorem sourceFieldCycleCurrent_positive_normalized :
    sourceFieldCycleCurrent.PosSemidef ∧ sourceFieldCycleCurrent.trace = 1 :=
  ⟨rememberedJoint_posSemidef _, rememberedJoint_trace _⟩

theorem sourceFieldCycleTarget_positive_normalized :
    sourceFieldCycleTarget.PosSemidef ∧ sourceFieldCycleTarget.trace = 1 :=
  ⟨fieldCycleAdvance_posSemidef _ sourceFieldCycleCurrent_positive_normalized.1,
    (fieldCycleAdvance_trace _).trans sourceFieldCycleCurrent_positive_normalized.2⟩

end

end LAlanine40K2025.Thermal.Work.Drive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
