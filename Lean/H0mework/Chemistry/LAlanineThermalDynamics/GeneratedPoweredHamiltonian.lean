import H0mework.Chemistry.LAlanineThermalDynamics.ResonantControllerInteraction
import H0mework.Chemistry.LAlanineWork.GeneratedFieldCapacity

/-! # The complete original source Hamiltonian fixes its controller coupling -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Source

open Collision Propagation.Interface Propagation.Dynamics Propagation.Source Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open scoped Matrix

noncomputable section

theorem pairHamiltonian_eq_source : pairHamiltonian energyHamiltonian = Work.Drive.fieldBaseline := rfl

def sourceInteraction := interaction energyHamiltonian

theorem sourceCoordinates_as_conjugation (A : SystemMatrix Basis) :
    Quantum.conjugation (star Preparation.sourceEnergyFrame) A = Preparation.energyCoordinates A := by
  rw [Quantum.conjugation_apply, Unitary.coe_star, star_star]
  rfl

theorem sourceHamiltonian_in_shared_frame :
    Quantum.conjugation (star Preparation.sourceEnergyFrame) (activeMatrix electronicSource) = energyHamiltonian :=
  (sourceCoordinates_as_conjugation _).trans Preparation.sourceHamiltonian_diagonal

theorem sourceRaising_nonzero : raising energyHamiltonian ≠ 0 := by
  intro zero
  let frame := star Preparation.sourceEnergyFrame
  have frameH : Quantum.conjugation frame (activeMatrix electronicSource) = energyHamiltonian :=
    sourceHamiltonian_in_shared_frame
  have covariant := shared_conjugation_raising frame (activeMatrix electronicSource)
  rw [frameH, zero] at covariant
  have rawZero : raising (activeMatrix electronicSource) = 0 := by
    apply (Unitary.conjStarAlgAut ℂ _ (Quantum.localUnitary frame frame)).injective
    exact covariant.trans (map_zero _).symm
  have commute := raising_zero_commutes (activeMatrix electronicSource) (initialDensityMatrix electronicSource)
    (activeMatrix_hermitian electronicSource) rawZero
  have opCommute := commute.map matrixOperatorEquiv
  exact operatorCommutator_ne_of_integer electronicSource 0 1 firstCommutator_nonzero
    (sub_eq_zero.mpr opCommute.eq)

theorem sourceInteraction_nonzero : sourceInteraction ≠ 0 :=
  interaction_nonzero energyHamiltonian sourceRaising_nonzero

theorem sourceInteraction_hermitian : sourceInteraction.IsHermitian := interaction_hermitian energyHamiltonian

theorem source_energy_resonance : Commute (bare energyHamiltonian) sourceInteraction :=
  bare_commutes_interaction energyHamiltonian energyHamiltonian_hermitian

/-- The energy frame is only a coordinate restriction of the original operator-generated ladder. -/
theorem sourceRaising_same_occurrence :
    raising energyHamiltonian =
      Quantum.localConjugation (star Preparation.sourceEnergyFrame) (star Preparation.sourceEnergyFrame)
        (raising (activeMatrix electronicSource)) := by
  rw [shared_conjugation_raising]
  exact congrArg raising sourceHamiltonian_in_shared_frame.symm

theorem sourceInteraction_same_occurrence :
    sourceInteraction = Unitary.conjStarAlgAut ℂ _ (controllerFrame (star Preparation.sourceEnergyFrame))
      (interaction (activeMatrix electronicSource)) := by
  rw [shared_conjugation_interaction]
  exact congrArg interaction sourceHamiltonian_in_shared_frame.symm

end

end LAlanine40K2025.Thermal.Powered.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
