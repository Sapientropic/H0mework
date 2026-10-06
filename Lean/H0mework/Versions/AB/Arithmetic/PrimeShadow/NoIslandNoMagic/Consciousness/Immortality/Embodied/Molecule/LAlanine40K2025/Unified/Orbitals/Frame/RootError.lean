import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Complex
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsPolarFrameTransportError
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsMatrixFrobeniusOperatorBound

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section

theorem complexMatrix_star (A : Matrix Basis Basis ℝ) :
    star (complexMatrix A) = complexMatrix A.transpose := by
  ext i j
  simp [complexMatrix,Matrix.star_apply,Matrix.transpose_apply]

theorem complexMatrix_nonnegative (A : Matrix Basis Basis ℝ) (positive : A.PosSemidef) :
    0 ≤ complexMatrix A := by
  let R := CFC.sqrt A
  have square : R*R = A := CFC.sqrt_mul_sqrt_self A positive.nonneg
  have symmetric : R.transpose = R := by
    have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
    ext i j
    have entry := congrArg (fun M : Matrix Basis Basis ℝ => M i j) h.eq
    simpa only [Matrix.conjTranspose_apply,Matrix.transpose_apply,star_trivial] using entry
  have h := star_mul_self_nonneg (complexMatrix R)
  rw [complexMatrix_star,symmetric,← complexMatrix_mul,square] at h
  exact h

theorem complexMatrix_sqrt (A : Matrix Basis Basis ℝ) (positive : A.PosSemidef) :
    complexMatrix (CFC.sqrt A) = CFC.sqrt (complexMatrix A) := by
  symm
  apply CFC.sqrt_unique
  · rw [← complexMatrix_mul,CFC.sqrt_mul_sqrt_self A positive.nonneg]
  · exact complexMatrix_nonnegative _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))

theorem source_root_error (positive : actualGram.PosDef) :
    ‖complexMatrix (CFC.sqrt actualGram)-1‖ ≤ ‖complexMatrix actualGram-1‖ := by
  rw [complexMatrix_sqrt actualGram positive.posSemidef]
  exact ElectronicFrame.Polar.sqrt_residual_norm _ (complexMatrix_nonnegative _ positive.posSemidef)

theorem complex_entry_norm (A : Matrix Basis Basis ℝ) (i j : Basis) :
    ‖complexMatrix A i j‖ = |A i j| := Complex.norm_real _

theorem gram_norm_from_entries (error : ℝ) (nonnegative : 0 ≤ error)
    (paid : ∀ i j, |(actualGram-1) i j| ≤ error) :
    ‖complexMatrix actualGram-1‖ ≤ 98*error := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by positivity)
  have each (i j : Basis) : ‖(complexMatrix actualGram-1) i j‖ ≤ error := by
    have identity : complexMatrix actualGram-1 = complexMatrix (actualGram-1) := by
      ext i j
      simp only [complexMatrix,Matrix.map_apply,Matrix.sub_apply,Complex.ofReal_sub,Matrix.one_apply]
      split_ifs <;> norm_num
    rw [identity,complex_entry_norm]
    exact paid i j
  calc
    _ ≤ ∑ _i : Basis, ∑ _j : Basis, error^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (each i j) 2))
    _ = _ := by norm_num [Fintype.card_fin]; ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
