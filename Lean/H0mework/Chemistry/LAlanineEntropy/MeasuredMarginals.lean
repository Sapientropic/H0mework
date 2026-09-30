import H0mework.Chemistry.LAlanineEntropy.PartialTraceCovariance
import H0mework.Chemistry.LAlanineEntropy.SpectralEntropy
import H0mework.Chemistry.LAlanineEntropy.ClassicalJointEntropy

/-! # Classical marginals and reduced quantum states come from one joint matrix -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem diagonalPMF_systemMarginal (joint : JointMatrix ι) (positive : joint.PosSemidef)
    (normalized : joint.trace = 1) :
    fstMarginal (diagonalPMF joint positive normalized) =
      diagonalPMF (systemReduce joint) (systemReduce_posSemidef _ positive)
        ((systemReduce_trace joint).trans normalized) := by
  classical
  ext i
  simp only [fstMarginal, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  have rowNonneg : ∀ a ∈ (Finset.univ : Finset ι), 0 ≤ (joint (i, a) (i, a)).re :=
    fun a _ => (Complex.nonneg_iff.mp (positive.diag_nonneg (i := (i, a)))).1
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (∑ a : ι, ENNReal.ofReal (joint (i, a) (i, a)).re) =
    ENNReal.ofReal ((∑ a : ι, joint (i, a) (i, a)).re)
  rw [Complex.re_sum]
  exact (ENNReal.ofReal_sum_of_nonneg rowNonneg).symm

theorem diagonalPMF_bathMarginal (joint : JointMatrix ι) (positive : joint.PosSemidef)
    (normalized : joint.trace = 1) :
    sndMarginal (diagonalPMF joint positive normalized) =
      diagonalPMF (bathReduce joint) (bathReduce_posSemidef _ positive)
        ((bathReduce_trace joint).trans normalized) := by
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

variable [DecidableEq ι]

theorem eigenbasis_measured_entropy (rho : SystemMatrix ι) (positive : rho.PosSemidef)
    (normalized : rho.trace = 1) :
    entropy (diagonalPMF (conjugation (star positive.isHermitian.eigenvectorUnitary) rho)
      (conjugation_posSemidef _ _ positive) ((conjugation_trace _ _).trans normalized)) =
      spectralEntropy rho positive normalized := by
  have samePMF : diagonalPMF (conjugation (star positive.isHermitian.eigenvectorUnitary) rho)
      (conjugation_posSemidef _ _ positive) ((conjugation_trace _ _).trans normalized) =
      spectralPMF rho positive normalized := by
    ext i
    apply (ENNReal.toReal_eq_toReal_iff' ((diagonalPMF _ _ _).apply_ne_top i)
      ((spectralPMF _ _ _).apply_ne_top i)).mp
    rw [diagonalPMF_toReal, spectralPMF_toReal]
    have diagonal := positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    change conjugation (star positive.isHermitian.eigenvectorUnitary) rho =
      Matrix.diagonal (fun j => (positive.isHermitian.eigenvalues j : ℂ)) at diagonal
    rw [diagonal, Matrix.diagonal_apply_eq]
    rfl
  rw [samePMF]
  rfl

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
