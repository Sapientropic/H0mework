import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Error
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Roots
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def factorQ {A B : Matrix α α ℚ} (G : SquareRoot.RootGram A B) : MatrixQ α α :=
  fun i j => (G.realPart i j,G.imagPart i j)

def factorInt {A B : Matrix α α ℚ} (G : SquareRoot.RootGram A B) : MatrixInt α α :=
  quantize (factorQ G)

def gramInt {A B : Matrix α α ℚ} (G : SquareRoot.RootGram A B) : MatrixInt α α :=
  multiply (factorInt G) (adjoint (factorInt G))

theorem factor_norm_bound_of_entries {A B : Matrix α α ℚ}
    (G : SquareRoot.RootGram A B) (small : Fintype.card α ≤ 64)
    (entries : ∀ i j, |G.realPart i j|+|G.imagPart i j| ≤ (1 : ℚ)) :
    ‖qvalue (factorQ G)‖ ≤ (64 : ℝ) := by
  have each (i j : α) : ‖qvalue (factorQ G) i j‖ ≤ (1 : ℝ) := by
    have bound : |(G.realPart i j : ℝ)|+|(G.imagPart i j : ℝ)| ≤ (1 : ℝ) := by
      exact_mod_cast entries i j
    change ‖((G.realPart i j : ℝ) : ℂ)+Complex.I*(((G.imagPart i j : ℝ) : ℂ))‖ ≤ 1
    calc
      _ ≤ ‖((G.realPart i j : ℝ) : ℂ)‖+
        ‖Complex.I*(((G.imagPart i j : ℝ) : ℂ))‖ := norm_add_le _ _
      _ = |(G.realPart i j : ℝ)|+|(G.imagPart i j : ℝ)| := by simp
      _ ≤ 1 := bound
  simpa only [mul_one] using
    norm_from_entries (qvalue (factorQ G)) 1 (by norm_num) small small each

theorem gram_int_error {A B : Matrix α α ℚ} (G : SquareRoot.RootGram A B)
    (small : Fintype.card α ≤ 64) (factorBound : ‖qvalue (factorQ G)‖ ≤ (64 : ℝ)) :
    ‖value (gramInt G)-qvalue (rootGramQ G)‖ ≤ (64/10^30 : ℝ) +
      (64/10^30 : ℝ)*((64 : ℝ)+(64/10^30 : ℝ))+(64 : ℝ)*(64/10^30 : ℝ) := by
  let F := qvalue (factorQ G)
  let FI := value (factorInt G)
  have approximated : ‖FI-F‖ ≤ (64/10^30 : ℝ) :=
    quantize_error (factorQ G) small small
  have fiBound : ‖FI‖ ≤ (64 : ℝ)+(64/10^30 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub FI F 0
    simp only [sub_zero] at triangle
    linarith only [triangle,approximated,factorBound]
  have rounded : ‖value (gramInt G)-FI*star FI‖ ≤ (64/10^30 : ℝ) := by
    simpa only [gramInt,FI,factorInt,value_adjoint,Matrix.star_eq_conjTranspose] using
      multiply_error (factorInt G) (adjoint (factorInt G)) small small
  have factorized : qvalue (rootGramQ G)=F*star F := by
    change qvalue (qmultiply (factorQ G) (qadjoint (factorQ G))) = _
    rw [qvalue_multiply,qvalue_adjoint]
    rfl
  have delta : FI*star FI-F*star F=(FI-F)*star FI+F*star (FI-F) := by
    rw [star_sub]
    noncomm_ring
  have product : ‖FI*star FI-F*star F‖ ≤
      (64/10^30 : ℝ)*((64 : ℝ)+(64/10^30 : ℝ))+(64 : ℝ)*(64/10^30 : ℝ) := by
    rw [delta]
    calc
      _ ≤ ‖(FI-F)*star FI‖+‖F*star (FI-F)‖ := norm_add_le _ _
      _ ≤ ‖FI-F‖*‖star FI‖+‖F‖*‖star (FI-F)‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = ‖FI-F‖*‖FI‖+‖F‖*‖FI-F‖ := by rw [norm_star,norm_star]
      _ ≤ _ := by
        gcongr
  rw [factorized]
  calc
    _ ≤ ‖value (gramInt G)-FI*star FI‖+‖FI*star FI-F*star F‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (64/10^30 : ℝ)+((64/10^30 : ℝ)*((64 : ℝ)+(64/10^30 : ℝ))+
      (64 : ℝ)*(64/10^30 : ℝ)) := add_le_add rounded product
    _ = _ := by ring

theorem gram_int_error_of_entries {A B : Matrix α α ℚ}
    (G : SquareRoot.RootGram A B) (small : Fintype.card α ≤ 64)
    (entries : ∀ i j, |G.realPart i j|+|G.imagPart i j| ≤ (1 : ℚ)) :
    ‖value (gramInt G)-qvalue (rootGramQ G)‖ ≤ (1/10^25 : ℝ) :=
  (gram_int_error G small (factor_norm_bound_of_entries G small entries)).trans (by norm_num)

theorem gram_int_reindex_error {β : Type*} [Fintype β] [DecidableEq β]
    {A B : Matrix α α ℚ} (G : SquareRoot.RootGram A B) (e : β ≃ α)
    (small : Fintype.card α ≤ 64)
    (entries : ∀ i j, |G.realPart i j|+|G.imagPart i j| ≤ (1 : ℚ)) :
    ‖value (submatrix (gramInt G) e e)-qvalue ((rootGramQ G).submatrix e e)‖ ≤
      (1/10^25 : ℝ) := by
  rw [value_submatrix,qvalue_submatrix]
  have same : (value (gramInt G)).submatrix e e-
      (qvalue (rootGramQ G)).submatrix e e =
      (value (gramInt G)-qvalue (rootGramQ G)).submatrix e e := by
    exact (congrFun (congrFun
      (Matrix.submatrix_sub (value (gramInt G)) (qvalue (rootGramQ G))) e) e).symm
  rw [same,Finite.reindex_norm]
  exact gram_int_error_of_entries G small entries


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
