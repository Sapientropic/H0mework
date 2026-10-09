import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Dynamics.WeightedResourceSpectralBounds
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedReservoirCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Source.PreparationEnergy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource

open Collision Load.Source
open scoped Matrix ComplexOrder
noncomputable section

def pcMatrixOf (rho : Current.FullJoint) := Collision.systemReduce (Powered.Dynamics.systemReduce rho)
def donorMatrixOf (rho : Current.FullJoint) := Collision.bathReduce (Powered.Dynamics.systemReduce rho)
def pcEnergyOf (rho : Current.FullJoint) : ℝ := energy Powered.Producer.poweredTotalHamiltonian (pcMatrixOf rho)
def donorEnergyOf (rho : Current.FullJoint) : ℝ := energy Powered.Producer.poweredTotalHamiltonian (donorMatrixOf rho)
def environmentEnergyOf (rho : Current.FullJoint) : ℝ :=
  energy (Powered.Dynamics.controllerHamiltonian 2) (Powered.Dynamics.controllerReduce rho)

theorem supply_pair (time : ℝ) (rho : Current.FullJoint) :
    Powered.Dynamics.systemReduce (Quantum.conjugation (Current.pulse time) rho) =
      Quantum.conjugation (Native.pairFlow time) (Powered.Dynamics.systemReduce rho) :=
  Load.Quantum.systemReduce_local_conjugation _ _ _

theorem supply_environment (time : ℝ) (rho : Current.FullJoint) :
    Powered.Dynamics.controllerReduce (Quantum.conjugation (Current.pulse time) rho) =
      Quantum.conjugation (Load.Recovery.Control.environmentUnitary time) (Powered.Dynamics.controllerReduce rho) :=
  Load.Quantum.controllerReduce_local_conjugation _ _ _

/-- The old exchange law applies to the actual pair marginal, including correlated conditional blocks. -/
theorem supply_energy_balance (time : ℝ) (rho : Current.FullJoint) :
    (pcEnergyOf (Quantum.conjugation (Current.pulse time) rho) - pcEnergyOf rho) +
      (donorEnergyOf (Quantum.conjugation (Current.pulse time) rho) - donorEnergyOf rho) = 0 := by
  have raw := Exchange.native_energy_balance Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian Native.sourceCoupling time
    (Powered.Dynamics.systemReduce rho)
  change energy Powered.Producer.poweredTotalHamiltonian
      (Collision.systemReduce (Quantum.conjugation (Native.pairFlow time) (Powered.Dynamics.systemReduce rho))) +
    energy Powered.Producer.poweredTotalHamiltonian
      (Collision.bathReduce (Quantum.conjugation (Native.pairFlow time) (Powered.Dynamics.systemReduce rho))) = _ at raw
  rw [← supply_pair] at raw
  change pcEnergyOf (Quantum.conjugation (Current.pulse time) rho) +
    donorEnergyOf (Quantum.conjugation (Current.pulse time) rho) = pcEnergyOf rho + donorEnergyOf rho at raw
  linarith

theorem supply_environment_energy (time : ℝ) (rho : Current.FullJoint) :
    environmentEnergyOf (Quantum.conjugation (Current.pulse time) rho) = environmentEnergyOf rho := by
  unfold environmentEnergyOf
  rw [supply_environment]
  simpa only [Quantum.conjugation_apply] using
    Recovery.PreparationEnergy.commuting_energy (Powered.Dynamics.controllerHamiltonian 2)
      (Powered.Dynamics.controllerReduce rho) (Load.Recovery.Control.environmentUnitary time)
      (Load.Recovery.Control.environmentUnitary_commutes time)

theorem donor_positive (rho : Current.FullJoint) (positive : rho.PosSemidef) :
    (donorMatrixOf rho).PosSemidef :=
  Collision.bathReduce_posSemidef _ (Powered.Dynamics.systemReduce_posSemidef _ positive)

theorem donor_trace (rho : Current.FullJoint) : (donorMatrixOf rho).trace = rho.trace :=
  (Collision.bathReduce_trace _).trans (Powered.Dynamics.systemReduce_trace rho)

def donorRemainingOf (rho : Current.FullJoint) : ℝ := donorEnergyOf rho -
  Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues
    (Spectrum.lastIndex (ι := PairController)) * rho.trace.re

theorem donor_remaining_range (rho : Current.FullJoint) (positive : rho.PosSemidef) :
    0 ≤ donorRemainingOf rho ∧ donorRemainingOf rho ≤
      (Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.firstIndex (ι := PairController)) -
        Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.lastIndex (ι := PairController))) *
      rho.trace.re := by
  have bounds := energy_weighted_spectral_bounds Powered.Producer.poweredTotalHamiltonian (donorMatrixOf rho)
    Powered.Producer.poweredTotalHamiltonian_hermitian (donor_positive rho positive)
  rw [donor_trace] at bounds
  constructor <;> dsimp only [donorRemainingOf, donorEnergyOf] <;> nlinarith [bounds.1, bounds.2]

theorem supply_paid_from_actual_remaining (time : ℝ) (rho : Current.FullJoint) (positive : rho.PosSemidef) :
    pcEnergyOf (Quantum.conjugation (Current.pulse time) rho) - pcEnergyOf rho ≤ donorRemainingOf rho := by
  have balance := supply_energy_balance time rho
  have floor := (donor_remaining_range (Quantum.conjugation (Current.pulse time) rho)
    (Quantum.conjugation_posSemidef _ _ positive)).1
  dsimp only [donorRemainingOf] at floor ⊢
  rw [Quantum.conjugation_trace] at floor
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
