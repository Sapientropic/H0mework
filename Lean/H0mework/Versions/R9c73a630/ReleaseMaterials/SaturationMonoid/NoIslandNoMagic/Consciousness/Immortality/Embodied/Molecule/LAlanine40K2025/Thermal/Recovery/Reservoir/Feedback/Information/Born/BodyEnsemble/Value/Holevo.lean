import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum.Coherence.Relative
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.BodyEnsemble.Value.QuantumGap

set_option autoImplicit false
set_option maxRecDepth 4096

namespace PhyslibCoherence

open scoped ComplexOrder
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixState (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) : MState ι where
  M := ⟨rho, positive.isHermitian⟩
  nonneg := HermitianMat.zero_le_iff.mpr positive
  tr := by
    change rho.trace.re = 1
    exact congrArg Complex.re normalized

theorem matrixState_m (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) : (matrixState rho positive normalized).m = rho := rfl

theorem matrixState_entropy (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) :
    Sᵥₙ (matrixState rho positive normalized) =
      Quantum.spectralEntropy rho positive normalized := by
  have hEig : (matrixState rho positive normalized).Hermitian.eigenvalues =
      positive.isHermitian.eigenvalues :=
    (((matrixState rho positive normalized).Hermitian).eigenvalues_eq_eigenvalues_iff
      positive.isHermitian).mpr (by rw [matrixState_m])
  unfold Sᵥₙ Quantum.spectralEntropy Population.entropy Hₛ
  simp only [H₁, Real.negMulLog]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [MState.spectrum, ProbDistribution.mk', ProbDistribution.prob,
    Quantum.spectralPMF_toReal]
  rw [hEig]

theorem diagonalDist_entropy_of_cells (ρ : MState ι) (p : PMF ι)
    (same : ∀ i, (p i).toReal = (ρ.m i i).re) :
    Hₛ (diagonalDist ρ) = Population.entropy p := by
  unfold Hₛ Population.entropy
  simp only [H₁, Real.negMulLog]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalDist_apply, same]
  ring

end
end PhyslibCoherence

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble

open PhyslibCoherence
open ValueCoarsening SourceGeneratedWorkInformation
noncomputable section

private theorem weights_sum : p0 + p1 = 1 := by
  simpa only [p0, p1] using SourceGeneratedConditionalWork.weights_sum receivedState

def sourceWeight : Prob := ⟨p0, ⟨p0_pos.le, by linarith [weights_sum, p1_pos.le]⟩⟩

def originalQuantumLeft : MState Current.FullIndex := matrixState rho0 rho0_positive rho0_trace
def originalQuantumRight : MState Current.FullIndex := matrixState rho1 rho1_positive rho1_trace
def originalQuantumBody : MState Current.FullIndex :=
  matrixState (bodyRead receivedState.joint) original_body_positive original_body_trace

def originalFrameLeft : MState Current.FullIndex := originalQuantumLeft.uConj spectralFrame
def originalFrameRight : MState Current.FullIndex := originalQuantumRight.uConj spectralFrame
def originalFrameBody : MState Current.FullIndex := originalQuantumBody.uConj spectralFrame

theorem originalFrameLeft_m : originalFrameLeft.m = Quantum.conjugation spectralFrame rho0 := by
  simp only [originalFrameLeft, MState.uConj, MState.m, HermitianMat.conj_apply_mat,
    Quantum.conjugation_apply]
  rfl

theorem originalFrameRight_m : originalFrameRight.m = Quantum.conjugation spectralFrame rho1 := by
  simp only [originalFrameRight, MState.uConj, MState.m, HermitianMat.conj_apply_mat,
    Quantum.conjugation_apply]
  rfl

theorem originalFrameBody_m : originalFrameBody.m =
    Quantum.conjugation spectralFrame (bodyRead receivedState.joint) := by
  simp only [originalFrameBody, MState.uConj, MState.m, HermitianMat.conj_apply_mat,
    Quantum.conjugation_apply]
  rfl

theorem originalFrameBody_mix :
    originalFrameBody = sourceWeight [originalFrameLeft ↔ originalFrameRight] := by
  apply MState.ext_m
  ext i j
  rw [originalFrameBody_m, PhyslibCoherence.mixedState_matrix,
    originalFrameLeft_m, originalFrameRight_m]
  simp only [sourceWeight, Subtype.coe_mk]
  have hp1 : 1 - p0 = p1 := by linarith [weights_sum]
  rw [hp1]
  have h := congrArg (fun M : Current.FullJoint =>
    (Quantum.conjugation spectralFrame M) i j) source_mixture
  simpa only [map_add, map_smul, Matrix.add_apply, Matrix.smul_apply,
    Complex.real_smul, smul_eq_mul] using h.symm

theorem originalFrameLeft_entropy : Sᵥₙ originalFrameLeft =
    Quantum.spectralEntropy rho0 rho0_positive rho0_trace := by
  simp only [originalFrameLeft, Sᵥₙ, MState.uConj_spectrum_eq]
  exact matrixState_entropy rho0 rho0_positive rho0_trace

theorem originalFrameRight_entropy : Sᵥₙ originalFrameRight =
    Quantum.spectralEntropy rho1 rho1_positive rho1_trace := by
  simp only [originalFrameRight, Sᵥₙ, MState.uConj_spectrum_eq]
  exact matrixState_entropy rho1 rho1_positive rho1_trace

theorem originalFrameBody_entropy : Sᵥₙ originalFrameBody =
    Quantum.spectralEntropy (bodyRead receivedState.joint)
      original_body_positive original_body_trace := by
  simp only [originalFrameBody, Sᵥₙ, MState.uConj_spectrum_eq]
  exact matrixState_entropy _ original_body_positive original_body_trace

theorem originalFrameLeft_diagonal_entropy : Hₛ (diagonalDist originalFrameLeft) =
    Population.entropy measured0 := by
  apply diagonalDist_entropy_of_cells
  intro i
  unfold measured0
  rw [Quantum.diagonalPMF_toReal, originalFrameLeft_m]

theorem originalFrameRight_diagonal_entropy : Hₛ (diagonalDist originalFrameRight) =
    Population.entropy measured1 := by
  apply diagonalDist_entropy_of_cells
  intro i
  unfold measured1
  rw [Quantum.diagonalPMF_toReal, originalFrameRight_m]

theorem originalFrameBody_diagonal_entropy : Hₛ (diagonalDist originalFrameBody) =
    Population.entropy (Quantum.diagonalPMF
      (Quantum.conjugation spectralFrame (bodyRead receivedState.joint))
      (Quantum.conjugation_posSemidef spectralFrame _ original_body_positive)
      ((Quantum.conjugation_trace spectralFrame _).trans original_body_trace)) := by
  apply diagonalDist_entropy_of_cells
  intro i
  rw [Quantum.diagonalPMF_toReal, originalFrameBody_m]

theorem originalFrameBody_coherence :
    Hₛ (diagonalDist originalFrameBody) - Sᵥₙ originalFrameBody = bodyCoherenceGap := by
  rw [originalFrameBody_diagonal_entropy, originalFrameBody_entropy]
  rfl

theorem originalFrameLeft_coherence :
    Hₛ (diagonalDist originalFrameLeft) - Sᵥₙ originalFrameLeft = leftCoherenceGap := by
  rw [originalFrameLeft_diagonal_entropy, originalFrameLeft_entropy]
  rfl

theorem originalFrameRight_coherence :
    Hₛ (diagonalDist originalFrameRight) - Sᵥₙ originalFrameRight = rightCoherenceGap := by
  rw [originalFrameRight_diagonal_entropy, originalFrameRight_entropy]
  rfl

theorem original_coherence_convex :
    bodyCoherenceGap ≤ p0 * leftCoherenceGap + p1 * rightCoherenceGap := by
  have h := realCoherence_mix_le originalFrameLeft originalFrameRight sourceWeight
  rw [← originalFrameBody_mix] at h
  rw [originalFrameBody_coherence, originalFrameLeft_coherence,
    originalFrameRight_coherence] at h
  simp only [sourceWeight, Subtype.coe_mk] at h
  have hp1 : 1 - p0 = p1 := by linarith [weights_sum]
  rwa [hp1] at h

theorem original_index_holevo_bound : indexedInformation ≤ sourceHolevo := by
  rw [indexed_information_quantum_gap]
  linarith [original_coherence_convex]

theorem original_value_holevo_bound :
    sourceMutualInformation + valueInformationLoss ≤ sourceHolevo := by
  rw [← indexedInformation_eq_value_add_loss]
  exact original_index_holevo_bound

def holevoInformationLoss : ℝ := sourceHolevo - indexedInformation

theorem holevoInformationLoss_nonnegative : 0 ≤ holevoInformationLoss :=
  sub_nonneg.mpr original_index_holevo_bound

theorem holevoInformationLoss_from_coherence :
    holevoInformationLoss =
      p0 * leftCoherenceGap + p1 * rightCoherenceGap - bodyCoherenceGap := by
  unfold holevoInformationLoss
  rw [indexed_information_quantum_gap]
  ring

theorem original_holevo_residual_account :
    sourceMutualInformation + valueInformationLoss + holevoInformationLoss =
      sourceHolevo := by
  rw [← indexedInformation_eq_value_add_loss]
  unfold holevoInformationLoss
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.SourceGeneratedBodyEnsemble
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
