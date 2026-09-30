import H0mework.Chemistry.LAlanineEntropy.MeasuredMarginals
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropyInvariance

/-! # Quantum entropy subadditivity from one joint state and its generated eigenbasis measurements -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem quantum_entropy_subadditive (joint : JointMatrix ι) (positive : joint.PosSemidef)
    (normalized : joint.trace = 1) :
    spectralEntropy joint positive normalized ≤
      spectralEntropy (systemReduce joint) (systemReduce_posSemidef joint positive)
        ((systemReduce_trace joint).trans normalized) +
      spectralEntropy (bathReduce joint) (bathReduce_posSemidef joint positive)
        ((bathReduce_trace joint).trans normalized) := by
  let rho := systemReduce joint
  let tau := bathReduce joint
  have rhoPositive : rho.PosSemidef := systemReduce_posSemidef joint positive
  have tauPositive : tau.PosSemidef := bathReduce_posSemidef joint positive
  have rhoTrace : rho.trace = 1 := (systemReduce_trace joint).trans normalized
  have tauTrace : tau.trace = 1 := (bathReduce_trace joint).trans normalized
  let U := star rhoPositive.isHermitian.eigenvectorUnitary
  let V := star tauPositive.isHermitian.eigenvectorUnitary
  let rotated := localConjugation U V joint
  have rotatedPositive : rotated.PosSemidef := localConjugation_posSemidef U V joint positive
  have rotatedTrace : rotated.trace = 1 := (localConjugation_trace U V joint).trans normalized
  have invariant : spectralEntropy rotated rotatedPositive rotatedTrace =
      spectralEntropy joint positive normalized :=
    spectralEntropy_unitary_conjugation joint positive normalized (localUnitary U V)
  have systemRead :
      entropy (diagonalPMF (systemReduce rotated) (systemReduce_posSemidef rotated rotatedPositive)
        ((systemReduce_trace rotated).trans rotatedTrace)) = spectralEntropy rho rhoPositive rhoTrace := by
    dsimp only [rotated]
    simp only [systemReduce_local_conjugation]
    exact eigenbasis_measured_entropy rho rhoPositive rhoTrace
  have bathRead :
      entropy (diagonalPMF (bathReduce rotated) (bathReduce_posSemidef rotated rotatedPositive)
        ((bathReduce_trace rotated).trans rotatedTrace)) = spectralEntropy tau tauPositive tauTrace := by
    dsimp only [rotated]
    simp only [bathReduce_local_conjugation]
    exact eigenbasis_measured_entropy tau tauPositive tauTrace
  calc
    spectralEntropy joint positive normalized = spectralEntropy rotated rotatedPositive rotatedTrace := invariant.symm
    _ ≤ entropy (diagonalPMF rotated rotatedPositive rotatedTrace) :=
      spectralEntropy_le_diagonal rotated rotatedPositive rotatedTrace
    _ ≤ entropy (fstMarginal (diagonalPMF rotated rotatedPositive rotatedTrace)) +
        entropy (sndMarginal (diagonalPMF rotated rotatedPositive rotatedTrace)) :=
      classical_entropy_subadditive _
    _ = _ := by
      rw [diagonalPMF_systemMarginal, diagonalPMF_bathMarginal, systemRead, bathRead]

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
