import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Source

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem restrict_mulVec {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (v : ι → ℂ) (k : κ) :
    (fun i : {i // label i = k} => (A *ᵥ v) i.val) =
      restrict label k A *ᵥ (fun i => v i.val) := by
  funext i
  change (∑ j, A i j * v j) = ∑ j : {j // label j = k}, A i j * v j
  apply sum_on_fiber
  intro j outside
  rw [kept i j (fun same => outside (same.symm.trans i.property)), zero_mul]

theorem eigenvector_block_zero {label : ι → κ} {A : Matrix ι ι ℂ}
    (kept : Preserves label A) (v : ι → ℂ) (lambda : ℂ)
    (eigen : A *ᵥ v = lambda • v) (k : κ)
    (resolvent : (restrict label k A - lambda • 1).det ≠ 0) :
    (fun i : {i // label i = k} => v i.val) = 0 := by
  have localEigen := congrArg (fun w : ι → ℂ => fun i : {i // label i = k} => w i.val) eigen
  rw [restrict_mulVec kept] at localEigen
  apply Matrix.mulVec_injective_of_det_ne_zero resolvent
  rw [Matrix.mulVec_zero, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact sub_eq_zero.mpr localEigen

omit [DecidableEq κ] in
theorem spectralPure_entry (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (a i j : ι) :
    Spectrum.spectralPure H hH a i j =
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) i a *
        star ((hH.eigenvectorUnitary : Matrix ι ι ℂ) j a) := by
  unfold Spectrum.spectralPure
  rw [Quantum.conjugation_apply, Matrix.star_eq_conjTranspose, Matrix.mul_apply]
  simp [Spectrum.basisPure, Matrix.mul_diagonal]

theorem spectralPure_one_block {label : ι → κ} {H : Matrix ι ι ℂ}
    (kept : Preserves label H) (hH : H.IsHermitian) (a : ι) (top : κ)
    (isolated : ∀ k, k ≠ top →
      (restrict label k H - (hH.eigenvalues a : ℂ) • 1).det ≠ 0) :
    ∀ i j, label i ≠ top ∨ label j ≠ top → Spectrum.spectralPure H hH a i j = 0 := by
  have vectorZero (i : ι) (outside : label i ≠ top) :
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) i a = 0 := by
    have localZero := eigenvector_block_zero kept
      (fun i => (hH.eigenvectorUnitary : Matrix ι ι ℂ) i a)
      (hH.eigenvalues a : ℂ) (by
        have eigen := hH.mulVec_eigenvectorBasis a
        funext i
        simpa only [Matrix.IsHermitian.eigenvectorUnitary_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using
          congrFun eigen i) (label i) (isolated (label i) outside)
    exact congrArg (fun v => v ⟨i,rfl⟩) localZero
  intro i j outside
  rw [spectralPure_entry]
  rcases outside with left | right
  · rw [vectorZero i left, zero_mul]
  · rw [vectorZero j right, star_zero, mul_zero]

open Propagation.Interface Load.Source

def donorEigenvalue : ℝ :=
  Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues Spectrum.firstIndex

def donorBlockResolvents (top : Sym2 Basis) : Prop :=
  ∀ k, k ≠ top →
    (restrict pcOrbit k Powered.Producer.poweredTotalHamiltonian - (donorEigenvalue : ℂ) • 1).det ≠ 0

theorem original_donor_one_block (top : Sym2 Basis) (isolated : donorBlockResolvents top) :
    ∀ i j, pcOrbit i ≠ top ∨ pcOrbit j ≠ top → Source.donor i j = 0 :=
  spectralPure_one_block source_hpc_preserves _ _ top isolated

theorem original_donor_preserves (top : Sym2 Basis) (isolated : donorBlockResolvents top) :
    Preserves pcOrbit Source.donor := by
  intro i j separated
  apply original_donor_one_block top isolated
  by_cases left : pcOrbit i = top
  · exact Or.inr (fun right => separated (left.trans right.symm))
  · exact Or.inl left

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
