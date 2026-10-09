import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.InstrumentState

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pointerDiagonal : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ where
  toFun A := Matrix.fromBlocks A 0 0 A
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := Matrix.fromBlocks_one
  map_add' A B := by ext i j; cases i <;> cases j <;> simp
  map_mul' A B := by rw [Matrix.fromBlocks_multiply]; simp
  commutes' c := by
    ext i j
    cases i <;> cases j <;> simp [Algebra.algebraMap_eq_smul_one,Matrix.one_apply]
  map_star' A := by simp only [Matrix.star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero]

def pointerQuarter : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 0 (-1) 1 0

theorem pointer_quarter_unitary : pointerQuarter (ι := ι) ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ := by
  constructor <;> simp [pointerQuarter,Matrix.star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]

theorem pointer_dilation_error (E F : Matrix ι ι ℂ) :
    ‖dilationMatrix E-dilationMatrix F‖ ≤ ‖effectRoot E-effectRoot F‖+‖complementRoot E-complementRoot F‖ := by
  have split : dilationMatrix E-dilationMatrix F =
      pointerDiagonal (effectRoot E-effectRoot F)+pointerDiagonal (complementRoot E-complementRoot F)*pointerQuarter := by
    change dilationMatrix E-dilationMatrix F = Matrix.fromBlocks _ 0 0 _+
      Matrix.fromBlocks _ 0 0 _*Matrix.fromBlocks 0 (-1) 1 0
    rw [Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> simp [dilationMatrix,sub_eq_add_neg,add_comm]
  rw [split]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact NonUnitalStarAlgHom.norm_apply_le pointerDiagonal _
  · rw [CStarRing.norm_mul_mem_unitary (pointerDiagonal (complementRoot E-complementRoot F)) (pointer_quarter_unitary (ι := ι))]
    exact NonUnitalStarAlgHom.norm_apply_le pointerDiagonal _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
