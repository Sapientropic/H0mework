import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.FullGamma.Residual
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.FullGamma.BlockEntropy

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble

open PhyslibCoherence FullGammaBlockEntropyOriginal
open SourceGeneratedWorkInformation ValueCoarsening
open scoped Matrix ComplexOrder
noncomputable section
attribute [local irreducible] Current.loadPulse Current.pulse Live.State.joint
  sourceTarget receivedState firstState

theorem originalBlockQuantumProduct_eq_projected :
    (blockDephase (ι := Current.FullIndex) originalQuantumProduct).relabel
      pointerIncidence = projectedState := by
  apply MState.ext_m
  rw [originalBlockQuantumProduct_source, projectedState_m]

theorem originalBlockQuantumEntropy :
    Sᵥₙ (blockDephase (ι := Current.FullIndex) originalQuantumProduct) =
      Real.negMulLog p0 + Real.negMulLog p1 +
        p0 * Quantum.spectralEntropy rho0 rho0_positive rho0_trace +
        p1 * Quantum.spectralEntropy rho1 rho1_positive rho1_trace := by
  have h := Sᵥₙ_relabel (blockDephase (ι := Current.FullIndex) originalQuantumProduct)
    pointerIncidence
  rw [originalBlockQuantumProduct_eq_projected] at h
  exact h.symm.trans projectedState_entropy

theorem originalPointerDiagonalEntropy :
    Sᵥₙ (diagonalState originalQuantumPointer) =
      Real.negMulLog p0 + Real.negMulLog p1 :=
  binaryDiagonalEntropy originalQuantumPointer p0 p1
    originalQuantumPointer_weights.1 originalQuantumPointer_weights.2

theorem originalBlockQuantumInformation_eq_holevo :
    qMutualInfo (blockDephase (ι := Current.FullIndex) originalQuantumProduct) =
      sourceHolevo := by
  rw [qMutualInfo, blockDephase_body, blockDephase_pointer_state,
    originalQuantumProduct_body_state, originalQuantumProduct_pointer_state,
    originalPointerDiagonalEntropy, originalBlockQuantumEntropy]
  rw [show Sᵥₙ originalQuantumBody =
    Quantum.spectralEntropy (bodyRead receivedState.joint)
      original_body_positive original_body_trace from
    matrixState_entropy _ _ _]
  unfold sourceHolevo
  ring

def fullGammaInformationResidual : ℝ :=
  (Sᵥₙ (blockDephase (ι := Current.FullIndex) originalQuantumProduct) -
      Sᵥₙ originalQuantumProduct) -
    (Sᵥₙ (diagonalState originalQuantumPointer) - Sᵥₙ originalQuantumPointer)

theorem originalFullQuantumInformation_coherence :
    qMutualInfo originalQuantumProduct = sourceHolevo +
      fullGammaInformationResidual ∧
    0 ≤ fullGammaInformationResidual ∧
    blockDephase (ι := Current.FullIndex) originalQuantumProduct ≠
      originalQuantumProduct ∧
    ¬ ∃ recover : MState (Current.FullIndex × Fin 2) →
        MState (Current.FullIndex × Fin 2),
      recover (blockDephase (ι := Current.FullIndex) originalQuantumProduct) =
        originalQuantumProduct ∧
      recover (blockDephase (ι := Current.FullIndex)
        (blockDephase (ι := Current.FullIndex) originalQuantumProduct)) =
        blockDephase (ι := Current.FullIndex) originalQuantumProduct := by
  refine ⟨?_, ?_, original_blockDephase_ne_full,
    blockDephase_no_common_recovery originalQuantumProduct original_blockDephase_ne_full⟩
  · rw [fullGammaInformationResidual, ← originalQuantumBlockResidual.1,
      ← originalBlockQuantumInformation_eq_holevo]
    ring
  · rw [fullGammaInformationResidual, ← originalQuantumBlockResidual.1]
    exact originalQuantumBlockResidual.2

theorem original_no_common_block_recovery :
    ¬ ∃ recover : MState (Current.FullIndex × Fin 2) →
        MState (Current.FullIndex × Fin 2),
      recover (blockDephase (ι := Current.FullIndex) originalQuantumProduct) =
        originalQuantumProduct ∧
      recover (blockDephase (ι := Current.FullIndex)
        (blockDephase (ι := Current.FullIndex) originalQuantumProduct)) =
        blockDephase (ι := Current.FullIndex) originalQuantumProduct :=
  originalFullQuantumInformation_coherence.2.2.2

theorem originalFullQuantumInformation_account :
    qMutualInfo originalQuantumProduct =
      sourceMutualInformation + valueInformationLoss + holevoInformationLoss +
        fullGammaInformationResidual ∧
      0 ≤ fullGammaInformationResidual := by
  constructor
  · rw [original_holevo_residual_account,
      originalFullQuantumInformation_coherence.1]
  · exact originalFullQuantumInformation_coherence.2.1

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
