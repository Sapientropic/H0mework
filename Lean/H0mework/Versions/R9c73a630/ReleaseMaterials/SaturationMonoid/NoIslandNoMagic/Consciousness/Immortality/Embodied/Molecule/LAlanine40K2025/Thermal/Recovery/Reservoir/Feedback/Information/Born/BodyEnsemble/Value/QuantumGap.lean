import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Value.BodyFrame

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble

open SourceGeneratedWorkInformation ValueCoarsening
open LAlanine40K2025.Thermal.Population

noncomputable section

def sourceHolevo : ℝ :=
  Quantum.spectralEntropy (bodyRead receivedState.joint) original_body_positive original_body_trace -
    p0 * Quantum.spectralEntropy rho0 rho0_positive rho0_trace -
    p1 * Quantum.spectralEntropy rho1 rho1_positive rho1_trace

def bodyCoherenceGap : ℝ :=
  entropy (Quantum.diagonalPMF
    (Quantum.conjugation spectralFrame (bodyRead receivedState.joint))
    (Quantum.conjugation_posSemidef spectralFrame _ original_body_positive)
    ((Quantum.conjugation_trace spectralFrame _).trans original_body_trace)) -
    Quantum.spectralEntropy (bodyRead receivedState.joint) original_body_positive original_body_trace

def leftCoherenceGap : ℝ := entropy measured0 - Quantum.spectralEntropy rho0 rho0_positive rho0_trace
def rightCoherenceGap : ℝ := entropy measured1 - Quantum.spectralEntropy rho1 rho1_positive rho1_trace

theorem indexed_information_quantum_gap :
    indexedInformation = sourceHolevo + bodyCoherenceGap -
      p0 * leftCoherenceGap - p1 * rightCoherenceGap := by
  have h := original_index_information_entropy
  rw [original_marginal_as_body_diagonal] at h
  rw [h]
  unfold sourceHolevo bodyCoherenceGap leftCoherenceGap rightCoherenceGap
  ring

theorem value_information_quantum_gap :
    sourceMutualInformation + valueInformationLoss =
      sourceHolevo + bodyCoherenceGap - p0 * leftCoherenceGap - p1 * rightCoherenceGap :=
  indexedInformation_eq_value_add_loss.symm.trans indexed_information_quantum_gap

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
