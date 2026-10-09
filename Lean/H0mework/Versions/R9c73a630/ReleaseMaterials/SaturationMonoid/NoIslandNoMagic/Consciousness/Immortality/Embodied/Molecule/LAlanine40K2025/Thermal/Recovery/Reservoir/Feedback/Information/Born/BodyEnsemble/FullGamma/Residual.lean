import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.FullGamma.Marginal
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum.Coherence.PointerBlock
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Cross.Source

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble

open PhyslibCoherence
open scoped Matrix ComplexOrder
noncomputable section
attribute [local irreducible] Current.loadPulse Current.pulse Live.State.joint
  sourceTarget receivedState firstState

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem blockDephase_source_matrix
    (rho : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    ((blockDephase (ι := ι)
      ((matrixState rho positive normalized).relabel pointerIncidence.symm)).relabel
        pointerIncidence).m = FullGammaCross.diagonalBlocksOnly rho := by
  ext x y
  cases x <;> cases y <;>
    simp [blockDephase_matrix, matrixState_m, MState.relabel_m,
      FullGammaCross.diagonalBlocksOnly, pointerIncidence] <;> rfl

theorem originalQuantumBlockInformation_le :
    qMutualInfo (blockDephase (ι := Current.FullIndex) originalQuantumProduct) ≤
      qMutualInfo originalQuantumProduct :=
  qMutualInfo_blockDephase_le originalQuantumProduct

theorem originalQuantumBlockResidual :
    qMutualInfo originalQuantumProduct -
        qMutualInfo (blockDephase (ι := Current.FullIndex) originalQuantumProduct) =
      (Sᵥₙ (blockDephase (ι := Current.FullIndex) originalQuantumProduct) -
          Sᵥₙ originalQuantumProduct) -
        (Sᵥₙ (diagonalState originalQuantumPointer) - Sᵥₙ originalQuantumPointer) ∧
      0 ≤ qMutualInfo originalQuantumProduct -
        qMutualInfo (blockDephase (ι := Current.FullIndex) originalQuantumProduct) := by
  constructor
  · rw [qMutualInfo_block_residual, originalQuantumProduct_pointer_state]
  · exact sub_nonneg.mpr originalQuantumBlockInformation_le

theorem originalBlockQuantumProduct_source :
    ((blockDephase (ι := Current.FullIndex) originalQuantumProduct).relabel
      pointerIncidence).m =
      FullGammaCross.diagonalBlocksOnly receivedState.joint := by
  simpa only [originalQuantumProduct, originalQuantumJoint] using
    blockDephase_source_matrix receivedState.joint receivedState.positive
      receivedState.normalized

theorem originalQuantumProduct_source :
    (originalQuantumProduct.relabel pointerIncidence).m =
      receivedState.joint := by
  rw [originalQuantumProduct, MState.relabel_relabel]
  have heq : pointerIncidence.trans pointerIncidence.symm =
      Equiv.refl PointerIndex := Equiv.ext (fun x => pointerIncidence.symm_apply_apply x)
  rw [heq, MState.relabel_refl]
  exact matrixState_m receivedState.joint receivedState.positive receivedState.normalized

theorem original_blockDephase_ne_full :
    blockDephase (ι := Current.FullIndex) originalQuantumProduct ≠
      originalQuantumProduct := by
  intro heq
  have hmat := congrArg (fun σ : MState (Current.FullIndex × Fin 2) =>
    (σ.relabel pointerIncidence).m) heq
  rw [originalBlockQuantumProduct_source, originalQuantumProduct_source] at hmat
  exact FullGammaCross.received_diagonal_blocks_incomplete hmat


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
