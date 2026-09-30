import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedThermalInputs
import H0mework.Chemistry.LAlanineThermalDynamics.PairHamiltonianFlow
import H0mework.Chemistry.LAlanineThermalDynamics.PairFlowFactorization

/-!
# A timed interaction acts on the retained pair

The source fixes one Hartree of exchange coupling. The duration is the existing
positive source clock in atomic units; it does not date the earlier integrated gate.
The update receives the whole current matrix, never a pair of reset marginals.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Source

open Propagation.Interface Propagation.Producer Preparation Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped ComplexOrder

noncomputable section

def pairCoupling : ℝ := 1

theorem energyHamiltonian_hermitian : energyHamiltonian.IsHermitian := by
  unfold energyHamiltonian
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff]

def timedPairAdvance (elapsed : ℝ) (current : JointMatrix Basis) : JointMatrix Basis :=
  pairAdvance energyHamiltonian pairCoupling elapsed current

def timedPairNativeStep (current : JointMatrix Basis) : JointMatrix Basis :=
  timedPairAdvance (nativeClockStep : ℝ) current

theorem timedPairAdvance_zero (current : JointMatrix Basis) :
    timedPairAdvance 0 current = current :=
  pairAdvance_zero energyHamiltonian energyHamiltonian_hermitian pairCoupling current

theorem timedPairAdvance_add (elapsed next : ℝ) (current : JointMatrix Basis) :
    timedPairAdvance (elapsed + next) current =
      timedPairAdvance elapsed (timedPairAdvance next current) :=
  pairAdvance_add energyHamiltonian energyHamiltonian_hermitian pairCoupling elapsed next current

theorem timedPairAdvance_posSemidef (elapsed : ℝ) (current : JointMatrix Basis)
    (positive : current.PosSemidef) : (timedPairAdvance elapsed current).PosSemidef :=
  pairAdvance_posSemidef energyHamiltonian energyHamiltonian_hermitian pairCoupling elapsed current positive

theorem timedPairAdvance_trace (elapsed : ℝ) (current : JointMatrix Basis) :
    (timedPairAdvance elapsed current).trace = current.trace :=
  pairAdvance_trace energyHamiltonian energyHamiltonian_hermitian pairCoupling elapsed current

theorem timedPairNativeStep_positive_duration : 0 < (nativeClockStep : ℝ) := by
  exact_mod_cast nativeClockStep_positive

/-- The numerical one- and two-dimensional blocks read the same generated exponential. -/
theorem timedPairPropagator_entry (elapsed : ℝ) (i a j b : Basis) :
    pairPropagatorMatrix energyHamiltonian pairCoupling elapsed (i, a) (j, b) =
      Complex.exp (-Complex.I * (elapsed : ℂ) * ((sourceEnergies i + sourceEnergies a : ℝ) : ℂ)) *
        partialSwap (Real.cos elapsed) (Real.sin elapsed) (i, a) (j, b) := by
  simpa only [energyHamiltonian, pairCoupling, one_mul] using
    pairPropagatorMatrix_diagonal_entry sourceEnergies pairCoupling elapsed i a j b

end

end LAlanine40K2025.Thermal.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
