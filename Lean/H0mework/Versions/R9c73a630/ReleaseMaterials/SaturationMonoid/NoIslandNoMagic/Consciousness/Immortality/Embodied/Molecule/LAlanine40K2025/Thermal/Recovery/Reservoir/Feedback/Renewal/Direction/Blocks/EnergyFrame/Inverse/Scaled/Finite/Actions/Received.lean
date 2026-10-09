import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Reverse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Load
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Tensor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
open Collision Propagation.Producer Load.Source Load.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def recoveryWord : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  Load.Quantum.localUnitary (Load.Recovery.Control.minimalPCUnitary (3*(nativeClockStep : ℝ)))
    (Load.Recovery.Control.environmentUnitary (3*(nativeClockStep : ℝ)))
def parentWord : Matrix.unitaryGroup (PairController × Fin 2) ℂ := Load.Quantum.localUnitary loadParentUnitary 1

def recoveryPolynomial : LoadedJoint := Matrix.kronecker recoveryPCPolynomial recoveryEnvironmentPolynomial
def parentPolynomial : LoadedJoint := Matrix.kronecker parentPCPolynomial 1

def calculatedReceivedWord : Matrix.unitaryGroup (PairController × Fin 2) ℂ := reframeUnitary installedLoadFrame Input.receivedWord

def finiteReceivedWord : LoadedJoint := recoveryPolynomial*loadPolynomial*parentPolynomial

theorem original_received_word_factors : calculatedReceivedWord=
    reframeUnitary installedLoadFrame recoveryWord * reframeUnitary installedLoadFrame (loadUnitary (nativeClockStep : ℝ)) *
      reframeUnitary installedLoadFrame parentWord := by
  change reframeUnitary installedLoadFrame (recoveryWord*loadUnitary (nativeClockStep : ℝ)*parentWord)=_
  rw [reframe_mul,reframe_mul]

theorem original_recovery_polynomial_error :
    ‖(reframeUnitary installedLoadFrame recoveryWord : LoadedJoint)-recoveryPolynomial‖ ≤ (167/10^15 : ℝ) := by
  rw [installedLoadFrame,recoveryWord,reframe_spectator]
  exact (approximated_tensor_error
    (reframeUnitary installedPCFrame (Load.Recovery.Control.minimalPCUnitary (3*(nativeClockStep : ℝ))))
    (Load.Recovery.Control.environmentUnitary (3*(nativeClockStep : ℝ))) recoveryPCPolynomial recoveryEnvironmentPolynomial
    (166/10^15) (1/10^18) original_recovery_PC_polynomial_error original_recovery_environment_polynomial_error).trans (by norm_num)

theorem original_parent_polynomial_error :
    ‖(reframeUnitary installedLoadFrame parentWord : LoadedJoint)-parentPolynomial‖ ≤ (111/10^15 : ℝ) := by
  rw [installedLoadFrame,parentWord,reframe_spectator]
  exact (approximated_tensor_error (reframeUnitary installedPCFrame loadParentUnitary)
    (1 : Matrix.unitaryGroup (Fin 2) ℂ) parentPCPolynomial 1 (111/10^15) 0
    original_parent_PC_polynomial_error (by simp)).trans (by norm_num)

theorem original_received_word_polynomial_error :
    ‖(calculatedReceivedWord : LoadedJoint)-finiteReceivedWord‖ ≤ (4/10^13 : ℝ) := by
  have first := Input.approximated_product_error
    (reframeUnitary installedLoadFrame recoveryWord) (reframeUnitary installedLoadFrame (loadUnitary (nativeClockStep : ℝ)))
    recoveryPolynomial loadPolynomial (167/10^15) (56/10^15)
    original_recovery_polynomial_error original_load_polynomial_error
  have firstBound := first.trans (show (167/10^15 : ℝ)+(1+167/10^15)*(56/10^15) ≤ 224/10^15 by norm_num)
  have second := Input.approximated_product_error
    (reframeUnitary installedLoadFrame recoveryWord*reframeUnitary installedLoadFrame (loadUnitary (nativeClockStep : ℝ)))
    (reframeUnitary installedLoadFrame parentWord) (recoveryPolynomial*loadPolynomial) parentPolynomial
    (224/10^15) (111/10^15) firstBound original_parent_polynomial_error
  rw [original_received_word_factors]
  exact second.trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
