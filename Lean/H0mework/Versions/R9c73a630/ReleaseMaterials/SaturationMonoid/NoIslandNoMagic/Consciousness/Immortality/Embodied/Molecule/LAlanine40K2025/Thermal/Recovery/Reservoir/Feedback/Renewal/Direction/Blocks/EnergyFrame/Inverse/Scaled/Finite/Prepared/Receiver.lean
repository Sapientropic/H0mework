import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Readout
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.FinitePair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem local_energy {ι : Type*} [Fintype ι] [DecidableEq ι] (U V : Matrix.unitaryGroup ι ℂ) (O rho : JointMatrix ι) :
    energy (Quantum.localConjugation U V O) (Quantum.localConjugation U V rho)=energy O rho :=
  Work.Capacity.energy_unitary_conjugation O rho (Quantum.localUnitary U V)

theorem local_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (U V : Matrix.unitaryGroup ι ℂ) (O : JointMatrix ι) :
    ‖Quantum.localConjugation U V O‖=‖O‖ :=
  StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ (Quantum.localUnitary U V)) O

theorem conjugation_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) :
    (Quantum.conjugation U A).IsHermitian := by
  change ((U : Matrix ι ι ℂ)*A*(U : Matrix ι ι ℂ)ᴴ).IsHermitian
  exact Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hermitian

def receivedObservable (O : LoadedJoint) : JointMatrix Propagation.Interface.Basis :=
  Quantum.localConjugation originalToCalculated originalToCalculated
    (preparationObservable (Quantum.conjugation (star Input.receivedWord) O))

theorem original_received_energy (O : LoadedJoint) :
    energy O Source.received.joint=energy (receivedObservable O)
      (Quantum.localConjugation originalToCalculated originalToCalculated Powered.Producer.sourceReceivedPair) := by
  rw [Input.original_received_from_preparation]
  have pullback : energy O (Quantum.conjugation Input.receivedWord Input.preparedBody)=
      energy (Quantum.conjugation (star Input.receivedWord) O) Input.preparedBody :=
    energy_pullback O Input.preparedBody Input.receivedWord
  rw [pullback,Input.preparedBody,preparation_energy]
  exact (local_energy originalToCalculated originalToCalculated _ _).symm

theorem received_observable_norm (O : LoadedJoint) (hermitian : O.IsHermitian) : ‖receivedObservable O‖ ≤ ‖O‖ := by
  rw [receivedObservable,local_norm]
  have h : (Quantum.conjugation (star Input.receivedWord) O).IsHermitian :=
    conjugation_hermitian (star Input.receivedWord) O hermitian
  apply (preparation_observable_norm _ h).trans
  exact le_of_eq (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ (star Input.receivedWord)) O)

theorem source_received_finite_energy_error (O : LoadedJoint) (hermitian : O.IsHermitian) :
    |energy O Source.received.joint-energy (receivedObservable O) Input.finitePair| ≤ (51/10^7 : ℝ)*‖O‖ := by
  rw [original_received_energy]
  exact (Input.original_finite_pair_energy_error (receivedObservable O)).trans
    (mul_le_mul_of_nonneg_left (received_observable_norm O hermitian) (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
