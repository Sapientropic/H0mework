import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Quantum.PartialTraceCovariance
import H0mework.Chemistry.LAlanineEntropy.MeasuredMarginals
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropyInvariance

/-! # Entropy subadditivity on the original unequal-dimensional joint carrier

Both marginal eigenbasis measurements come from one local conjugation of the
actual joint state. Existing spectral and classical entropy consumers finish the bound.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem diagonalPMF_systemMarginal (joint : Matrix (ι × κ) (ι × κ) ℂ)
    (positive : joint.PosSemidef) (normalized : joint.trace = 1) :
    fstMarginal (diagonalPMF joint positive normalized) =
      diagonalPMF (systemReduce joint) (systemReduce_posSemidef _ positive)
        ((systemReduce_trace joint).trans normalized) := by
  classical
  ext i
  simp only [fstMarginal, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  have rowNonneg : ∀ a ∈ (Finset.univ : Finset κ), 0 ≤ (joint (i, a) (i, a)).re :=
    fun a _ => (Complex.nonneg_iff.mp (positive.diag_nonneg (i := (i, a)))).1
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (∑ a : κ, ENNReal.ofReal (joint (i, a) (i, a)).re) =
    ENNReal.ofReal ((∑ a : κ, joint (i, a) (i, a)).re)
  rw [Complex.re_sum]
  exact (ENNReal.ofReal_sum_of_nonneg rowNonneg).symm

private theorem diagonalPMF_controllerMarginal (joint : Matrix (ι × κ) (ι × κ) ℂ)
    (positive : joint.PosSemidef) (normalized : joint.trace = 1) :
    sndMarginal (diagonalPMF joint positive normalized) =
      diagonalPMF (controllerReduce joint) (controllerReduce_posSemidef _ positive)
        ((controllerReduce_trace joint).trans normalized) := by
  classical
  ext a
  simp only [sndMarginal, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  have columnNonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (joint (i, a) (i, a)).re :=
    fun i _ => (Complex.nonneg_iff.mp (positive.diag_nonneg (i := (i, a)))).1
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (∑ i : ι, ENNReal.ofReal (joint (i, a) (i, a)).re) =
    ENNReal.ofReal ((∑ i : ι, joint (i, a) (i, a)).re)
  rw [Complex.re_sum]
  exact (ENNReal.ofReal_sum_of_nonneg columnNonneg).symm

variable [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The full joint entropy is bounded by its two generated marginal entropies. -/
theorem quantum_entropy_subadditive (joint : Matrix (ι × κ) (ι × κ) ℂ)
    (positive : joint.PosSemidef) (normalized : joint.trace = 1) :
    spectralEntropy joint positive normalized ≤
      spectralEntropy (systemReduce joint) (systemReduce_posSemidef joint positive)
        ((systemReduce_trace joint).trans normalized) +
      spectralEntropy (controllerReduce joint) (controllerReduce_posSemidef joint positive)
        ((controllerReduce_trace joint).trans normalized) := by
  let rho := systemReduce joint
  let tau := controllerReduce joint
  have rhoPositive : rho.PosSemidef := systemReduce_posSemidef joint positive
  have tauPositive : tau.PosSemidef := controllerReduce_posSemidef joint positive
  have rhoTrace : rho.trace = 1 := (systemReduce_trace joint).trans normalized
  have tauTrace : tau.trace = 1 := (controllerReduce_trace joint).trans normalized
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
        ((systemReduce_trace rotated).trans rotatedTrace)) =
          spectralEntropy rho rhoPositive rhoTrace := by
    dsimp only [rotated]
    simp only [systemReduce_local_conjugation]
    exact eigenbasis_measured_entropy rho rhoPositive rhoTrace
  have controllerRead :
      entropy (diagonalPMF (controllerReduce rotated)
        (controllerReduce_posSemidef rotated rotatedPositive)
        ((controllerReduce_trace rotated).trans rotatedTrace)) =
          spectralEntropy tau tauPositive tauTrace := by
    dsimp only [rotated]
    simp only [controllerReduce_local_conjugation]
    exact eigenbasis_measured_entropy tau tauPositive tauTrace
  calc
    spectralEntropy joint positive normalized =
        spectralEntropy rotated rotatedPositive rotatedTrace := invariant.symm
    _ ≤ entropy (diagonalPMF rotated rotatedPositive rotatedTrace) :=
      spectralEntropy_le_diagonal rotated rotatedPositive rotatedTrace
    _ ≤ entropy (fstMarginal (diagonalPMF rotated rotatedPositive rotatedTrace)) +
        entropy (sndMarginal (diagonalPMF rotated rotatedPositive rotatedTrace)) :=
      classical_entropy_subadditive _
    _ = _ := by
      rw [diagonalPMF_systemMarginal, diagonalPMF_controllerMarginal, systemRead, controllerRead]

end

end LAlanine40K2025.Thermal.Load.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
