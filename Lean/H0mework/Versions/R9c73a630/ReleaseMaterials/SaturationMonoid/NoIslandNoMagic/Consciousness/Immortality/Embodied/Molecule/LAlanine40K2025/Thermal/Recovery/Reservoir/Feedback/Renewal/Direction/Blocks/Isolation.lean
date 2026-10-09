import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Hpc
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Donor

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
open Collision Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem energy_basisPure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (i : ι) : energy H (Spectrum.basisPure i) = (H i i).re := by
  simp [energy, Spectrum.basisPure, Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

theorem donorEigenvalue_ge_diagonal (a : Basis) :
    2 * Preparation.sourceEnergies a + 3 ≤ donorEigenvalue := by
  have upper := (Spectrum.energy_spectral_bounds Powered.Producer.poweredTotalHamiltonian
    (Spectrum.basisPure ((a,a),(1 : Fin 2))) Powered.Producer.poweredTotalHamiltonian_hermitian
    (Spectrum.basisPure_positive _) (Spectrum.basisPure_trace _)).2
  rw [energy_basisPure] at upper
  have diagonal := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1)
    (original_hpc_diagonal_block a)
  change Powered.Producer.poweredTotalHamiltonian ((a,a),(1 : Fin 2)) ((a,a),(1 : Fin 2)) =
    2*(Preparation.sourceEnergies a : ℂ)+3 at diagonal
  rw [diagonal] at upper
  norm_num [Complex.add_re, Complex.mul_re] at upper
  exact upper

/-- A primitive one-body spectral packet; its inequalities carry no transfer or load conclusion. -/
def SourceEnergyIsolation (top : Basis) : Prop :=
  (31/10 : ℝ) < Preparation.sourceEnergies top ∧
  Preparation.sourceEnergies top < (63/20 : ℝ) ∧
  ∀ i, i ≠ top → Preparation.sourceEnergies i < 3

theorem source_isolation_resolvents (top : Basis) (isolated : SourceEnergyIsolation top) :
    donorBlockResolvents s(top,top) := by
  have lower : (46/5 : ℝ) < donorEigenvalue := by
    have fromTop := donorEigenvalue_ge_diagonal top
    linarith [isolated.1]
  have allUpper (i : Basis) : Preparation.sourceEnergies i < (63/20 : ℝ) := by
    by_cases same : i = top
    · simpa only [same] using isolated.2.1
    · linarith [isolated.2.2 i same]
  intro k outside
  obtain ⟨⟨a,b⟩, rfl⟩ := Sym2.mk_surjective k
  change (restrict pcOrbit s(a,b) Powered.Producer.poweredTotalHamiltonian -
    (donorEigenvalue : ℂ) • 1).det ≠ 0
  by_cases diagonal : a = b
  · subst b
    have different : a ≠ top := by
      intro same
      apply outside
      subst a
      rfl
    rw [original_diagonal_resolvent]
    have high := isolated.2.2 a different
    apply mul_ne_zero
    · exact_mod_cast (sub_ne_zero.mpr (ne_of_lt (show 2 * Preparation.sourceEnergies a + 1 < donorEigenvalue by linarith)))
    · exact_mod_cast (sub_ne_zero.mpr (ne_of_lt (show 2 * Preparation.sourceEnergies a + 3 < donorEigenvalue by linarith)))
  · rw [original_offDiagonal_resolvent a b diagonal]
    have sumUpper : Preparation.sourceEnergies a + Preparation.sourceEnergies b + 3 < donorEigenvalue := by
      by_cases same : a = top
      · have other : b ≠ top := fun equality => diagonal (same.trans equality.symm)
        linarith [allUpper a, isolated.2.2 b other]
      · linarith [isolated.2.2 a same, allUpper b]
    have leftUpper : 2 * Preparation.sourceEnergies a + 1 < donorEigenvalue := by linarith [allUpper a]
    have rightUpper : 2 * Preparation.sourceEnergies b + 1 < donorEigenvalue := by linarith [allUpper b]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact_mod_cast (sub_ne_zero.mpr (ne_of_lt
            (show Preparation.sourceEnergies a + Preparation.sourceEnergies b - 1 < donorEigenvalue by linarith)))
        · exact_mod_cast (sub_ne_zero.mpr (ne_of_lt sumUpper))
      · exact_mod_cast (sub_ne_zero.mpr (ne_of_lt leftUpper))
    · exact_mod_cast (sub_ne_zero.mpr (ne_of_lt rightUpper))

def secondEnergyIndex : Basis := Work.Capacity.spectralIndex.symm
  ⟨1, by norm_num [Basis]⟩

/-- Two scalar source eigenvalue enclosures generate every one-body exclusion. -/
def SourceTopPairBounds : Prop :=
  (31/10 : ℝ) < Preparation.sourceEnergies Spectrum.firstIndex ∧
  Preparation.sourceEnergies Spectrum.firstIndex < (63/20 : ℝ) ∧
  Preparation.sourceEnergies secondEnergyIndex < 3

theorem source_top_pair_isolation (bounded : SourceTopPairBounds) :
    SourceEnergyIsolation Spectrum.firstIndex := by
  refine ⟨bounded.1, bounded.2.1, ?_⟩
  intro i different
  have indexPositive : 0 < (Work.Capacity.spectralIndex i).val := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply different
    apply Work.Capacity.spectralIndex.injective
    rw [Spectrum.firstIndex, Equiv.apply_symm_apply]
    apply Fin.ext
    exact zero
  have ordered : Preparation.sourceEnergies i ≤ Preparation.sourceEnergies secondEnergyIndex := by
    change (Propagation.Dynamics.activeMatrix_hermitian Propagation.Source.electronicSource).eigenvalues₀
      (Work.Capacity.spectralIndex i) ≤
      (Propagation.Dynamics.activeMatrix_hermitian Propagation.Source.electronicSource).eigenvalues₀
        (Work.Capacity.spectralIndex secondEnergyIndex)
    rw [secondEnergyIndex, Equiv.apply_symm_apply]
    apply Matrix.IsHermitian.eigenvalues₀_antitone
    exact indexPositive
  exact ordered.trans_lt bounded.2.2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
