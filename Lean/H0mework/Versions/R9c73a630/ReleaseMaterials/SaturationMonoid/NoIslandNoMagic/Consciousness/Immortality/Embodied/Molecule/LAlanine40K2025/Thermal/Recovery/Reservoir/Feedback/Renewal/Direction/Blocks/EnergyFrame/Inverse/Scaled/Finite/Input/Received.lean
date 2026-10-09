import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Pointer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Propagation.Interface Propagation.Producer Load.Source Load.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def receivedWord : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  Load.Quantum.localUnitary
    (Load.Recovery.Control.minimalPCUnitary (3*(nativeClockStep : ℝ)))
    (Load.Recovery.Control.environmentUnitary (3*(nativeClockStep : ℝ))) *
  loadUnitary (nativeClockStep : ℝ) * Load.Quantum.localUnitary loadParentUnitary 1

def preparedBody : LoadedJoint := Matrix.kronecker (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair) environmentState

theorem tensor_left_action {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    Matrix.kronecker (Unitary.conjStarAlgAut ℂ _ U A) B=
      Quantum.conjugation (Load.Quantum.localUnitary U 1) (Matrix.kronecker A B) := by
  change _=Load.Quantum.localConjugation U 1 (Matrix.kronecker A B)
  rw [Load.Quantum.localConjugation_tensor]
  have one : Quantum.conjugation (1 : Matrix.unitaryGroup κ ℂ) B=B := by
    simp only [Quantum.conjugation_apply,Submonoid.coe_one,star_one,Matrix.one_mul,Matrix.mul_one]
  rw [one]
  rfl

theorem original_received_from_preparation : Source.received.joint=Quantum.conjugation receivedWord preparedBody := by
  change Recovery.Producer.recoveryStateFirst.joint=_
  rw [Recovery.Producer.recoveryStateFirst,Recovery.Producer.recoveryStep_joint,
    Recovery.Producer.recoveryReceived_actual,loadStateNext_joint,loadInitialState_received]
  unfold loadInitialJoint
  rw [loadParent_joint_from_preparation]
  have tensor : Matrix.kronecker
      (Unitary.conjStarAlgAut ℂ _ loadParentUnitary (Powered.Dynamics.chargedInput Powered.Producer.sourceReceivedPair)) environmentState=
      Quantum.conjugation (Load.Quantum.localUnitary loadParentUnitary 1) preparedBody := by
    exact tensor_left_action loadParentUnitary _ environmentState
  rw [tensor]
  change Quantum.conjugation (Load.Quantum.localUnitary _ _)
    (Quantum.conjugation (loadUnitary (nativeClockStep : ℝ))
      (Quantum.conjugation (Load.Quantum.localUnitary loadParentUnitary 1) preparedBody))=_
  rw [Environment.conjugation_comp,Environment.conjugation_comp]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
