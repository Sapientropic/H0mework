import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PurePointerPreparation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerBlockReadout
import H0mework.Physics.Lie.P286
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open scoped Matrix Matrix.Norms.Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def blockUnitary (U V : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup (ι ⊕ ι) ℂ :=
  ⟨Matrix.fromBlocks (U : Matrix ι ι ℂ) 0 0 (V : Matrix ι ι ℂ),
    SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal.fromBlocks_zero_mem_unitary U.property V.property⟩

omit [Fintype ι] [DecidableEq ι] in
theorem fromBlocks_diagonal_incidence (A D : Matrix ι ι ℂ) :
    Matrix.fromBlocks A 0 0 D =
      (Matrix.blockDiagonal (fun b : Fin 2 => if b = 0 then A else D)).submatrix
        pointerIncidence pointerIncidence := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.blockDiagonal, pointerIncidence]

theorem exp_pointer_reindex (M : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) :
    NormedSpace.exp (M.submatrix pointerIncidence pointerIncidence) =
      (NormedSpace.exp M).submatrix pointerIncidence pointerIncidence := by
  let f := Matrix.reindexRingEquiv ℂ (pointerIncidence (ι := ι)).symm
  have continuousMap : Continuous f := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply (pointerIncidence j)).comp (continuous_apply (pointerIncidence i))
  exact (NormedSpace.map_exp f continuousMap M).symm

theorem exp_fromBlocks_diagonal (A D : Matrix ι ι ℂ) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D) := by
  rw [fromBlocks_diagonal_incidence, exp_pointer_reindex, Matrix.exp_blockDiagonal,
    fromBlocks_diagonal_incidence]
  apply congrArg (fun v : Fin 2 → Matrix ι ι ℂ =>
    (Matrix.blockDiagonal v).submatrix pointerIncidence pointerIncidence)
  funext b
  exact (Pi.coe_exp (fun b : Fin 2 => if b = 0 then A else D) b).trans (by
    split_ifs <;> rfl)

theorem blockUnitary_conjugation_blocks (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    (blockUnitary U V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * joint *
      star (blockUnitary U V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) =
    Matrix.fromBlocks
      ((U : Matrix ι ι ℂ) * joint.toBlocks₁₁ * star (U : Matrix ι ι ℂ))
      ((U : Matrix ι ι ℂ) * joint.toBlocks₁₂ * star (V : Matrix ι ι ℂ))
      ((V : Matrix ι ι ℂ) * joint.toBlocks₂₁ * star (U : Matrix ι ι ℂ))
      ((V : Matrix ι ι ℂ) * joint.toBlocks₂₂ * star (V : Matrix ι ι ℂ)) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks joint]
  simp [blockUnitary, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]

theorem blockUnitary_conjugation_diagonal_left (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    ((blockUnitary U V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * joint *
      star (blockUnitary U V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)).toBlocks₁₁ =
    (U : Matrix ι ι ℂ) * joint.toBlocks₁₁ * star (U : Matrix ι ι ℂ) := by
  rw [blockUnitary_conjugation_blocks, Matrix.toBlocks_fromBlocks₁₁]

theorem blockUnitary_conjugation_diagonal_right (U V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    ((blockUnitary U V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * joint *
      star (blockUnitary U V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)).toBlocks₂₂ =
    (V : Matrix ι ι ℂ) * joint.toBlocks₂₂ * star (V : Matrix ι ι ℂ) := by
  rw [blockUnitary_conjugation_blocks, Matrix.toBlocks_fromBlocks₂₂]

theorem blockUnitary_common_phase_body (U : Matrix.unitaryGroup ι ℂ) (z : unitary ℂ)
    (joint : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    bodyRead ((blockUnitary U (z • U) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * joint *
      star (blockUnitary U (z • U) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)) =
    (U : Matrix ι ι ℂ) * bodyRead joint * star (U : Matrix ι ι ℂ) := by
  rw [bodyRead, blockUnitary_conjugation_diagonal_left, blockUnitary_conjugation_diagonal_right,
    bodyRead, Matrix.mul_add, Matrix.add_mul]
  congr 1
  change (((z : ℂ) • (U : Matrix ι ι ℂ)) * joint.toBlocks₂₂ *
    star ((z : ℂ) • (U : Matrix ι ι ℂ))) = _
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Unitary.star_mul_self_of_mem z.property, one_smul]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
