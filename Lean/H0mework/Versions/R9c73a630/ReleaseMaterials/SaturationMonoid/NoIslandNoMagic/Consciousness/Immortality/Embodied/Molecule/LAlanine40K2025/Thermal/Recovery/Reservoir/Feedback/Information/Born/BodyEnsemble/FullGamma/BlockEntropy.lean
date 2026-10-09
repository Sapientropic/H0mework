import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum.Coherence.BlockEntropy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Value.Holevo
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Cross.Source

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback
namespace FullGammaBlockEntropyOriginal

open _root_.FullGammaBlockEntropy
open SourceGeneratedBodyEnsemble FullGammaCross
open scoped Matrix ComplexOrder
noncomputable section

private theorem real_smul_matrix {ι : Type*} (p : ℝ) (M : Matrix ι ι ℂ) :
    p • M = (p : ℂ) • M := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

private theorem weights_sum : p0 + p1 = 1 := by
  simpa only [p0, p1] using
    SourceGeneratedConditionalWork.weights_sum
      receivedState

def projectedState : MState (Current.FullIndex ⊕ Current.FullIndex) :=
  blockState p0 p1 p0_pos.le p1_pos.le weights_sum
    originalQuantumLeft originalQuantumRight

theorem projectedState_m : projectedState.m = diagonalBlocksOnly receivedState.joint := by
  have h0 : (p0 : ℂ) • rho0 = sigma0 := weighted_unnormalize sigma0 p0 p0_pos
  have h1 : (p1 : ℂ) • rho1 = sigma1 := weighted_unnormalize sigma1 p1 p1_pos
  change blockMatrix (p0 • originalQuantumLeft.m) (p1 • originalQuantumRight.m) =
    Matrix.fromBlocks receivedState.joint.toBlocks₁₁ 0 0 receivedState.joint.toBlocks₂₂
  have hleft : p0 • originalQuantumLeft.m = receivedState.joint.toBlocks₁₁ := by
    change p0 • rho0 = sigma0
    exact (real_smul_matrix p0 rho0).trans h0
  have hright : p1 • originalQuantumRight.m = receivedState.joint.toBlocks₂₂ := by
    change p1 • rho1 = sigma1
    exact (real_smul_matrix p1 rho1).trans h1
  rw [hleft, hright]
  rfl

theorem projectedState_entropy :
    Sᵥₙ projectedState = Real.negMulLog p0 + Real.negMulLog p1 +
      p0 * Quantum.spectralEntropy rho0 rho0_positive rho0_trace +
      p1 * Quantum.spectralEntropy rho1 rho1_positive rho1_trace := by
  simpa only [projectedState, originalQuantumLeft, originalQuantumRight,
    PhyslibCoherence.matrixState_entropy] using
    blockState_entropy p0 p1 p0_pos.le p1_pos.le weights_sum
      originalQuantumLeft originalQuantumRight

end
end FullGammaBlockEntropyOriginal
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
