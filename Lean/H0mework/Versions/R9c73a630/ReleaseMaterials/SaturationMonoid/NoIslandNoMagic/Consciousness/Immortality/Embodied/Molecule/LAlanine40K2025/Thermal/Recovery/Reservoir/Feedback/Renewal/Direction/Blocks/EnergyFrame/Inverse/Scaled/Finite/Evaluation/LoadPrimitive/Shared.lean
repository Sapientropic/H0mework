import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Splice
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Coefficients
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Similarity

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open scoped Matrix BigOperators
noncomputable section

def starHamiltonian (s d : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := s • 1+starCore d

def sharedExpected (x y : ℝ) : Matrix RawIndex RawIndex ℂ := raw (starHamiltonian ((x : ℂ)+y+1) ((x : ℂ)-y)) (starHamiltonian ((x : ℂ)+y+3) ((x : ℂ)-y)) ((x : ℂ)+y+5) ((x : ℂ)+y-1)

private theorem shared_row0 (x y : ℝ) (j : RawIndex) :
    sharedHamiltonian x y (joinEquiv (Sum.inl 0)) (joinEquiv j)=sharedExpected x y (Sum.inl 0) j := by
  simp only [sharedExpected,raw,starHamiltonian,Matrix.one_fin_three]
  rcases j with (j | (j | (j | j))) <;> fin_cases j <;>
    norm_num [sharedHamiltonian,joinEquiv,starCore,Matrix.fromBlocks,Matrix.submatrix,finSumFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

private theorem shared_row1 (x y : ℝ) (j : RawIndex) :
    sharedHamiltonian x y (joinEquiv (Sum.inl 1)) (joinEquiv j)=sharedExpected x y (Sum.inl 1) j := by
  simp only [sharedExpected,raw,starHamiltonian,Matrix.one_fin_three]
  rcases j with (j | (j | (j | j))) <;> fin_cases j <;>
    norm_num [sharedHamiltonian,joinEquiv,starCore,Matrix.fromBlocks,Matrix.submatrix,finSumFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

private theorem shared_row2 (x y : ℝ) (j : RawIndex) :
    sharedHamiltonian x y (joinEquiv (Sum.inl 2)) (joinEquiv j)=sharedExpected x y (Sum.inl 2) j := by
  simp only [sharedExpected,raw,starHamiltonian,Matrix.one_fin_three]
  rcases j with (j | (j | (j | j))) <;> fin_cases j <;>
    norm_num [sharedHamiltonian,joinEquiv,starCore,Matrix.fromBlocks,Matrix.submatrix,finSumFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  all_goals rfl

private theorem shared_row3 (x y : ℝ) (j : RawIndex) :
    sharedHamiltonian x y (joinEquiv (Sum.inr (Sum.inl 0))) (joinEquiv j)=sharedExpected x y (Sum.inr (Sum.inl 0)) j := by
  simp only [sharedExpected,raw,starHamiltonian,Matrix.one_fin_three]
  rcases j with (j | (j | (j | j))) <;> fin_cases j <;>
    norm_num [sharedHamiltonian,joinEquiv,starCore,Matrix.fromBlocks,Matrix.submatrix,finSumFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

private theorem shared_row4 (x y : ℝ) (j : RawIndex) :
    sharedHamiltonian x y (joinEquiv (Sum.inr (Sum.inr (Sum.inl 0)))) (joinEquiv j)=sharedExpected x y (Sum.inr (Sum.inr (Sum.inl 0))) j := by
  simp only [sharedExpected,raw,starHamiltonian,Matrix.one_fin_three]
  rcases j with (j | (j | (j | j))) <;> fin_cases j <;>
    norm_num [sharedHamiltonian,joinEquiv,starCore,Matrix.fromBlocks,Matrix.submatrix,finSumFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

private theorem shared_row5 (x y : ℝ) (j : RawIndex) :
    sharedHamiltonian x y (joinEquiv (Sum.inr (Sum.inr (Sum.inr 0)))) (joinEquiv j)=sharedExpected x y (Sum.inr (Sum.inr (Sum.inr 0))) j := by
  simp only [sharedExpected,raw,starHamiltonian,Matrix.one_fin_three]
  rcases j with (j | (j | (j | j))) <;> fin_cases j <;>
    norm_num [sharedHamiltonian,joinEquiv,starCore,Matrix.fromBlocks,Matrix.submatrix,finSumFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

private theorem shared_row6 (x y : ℝ) (j : RawIndex) :
    sharedHamiltonian x y (joinEquiv (Sum.inr (Sum.inr (Sum.inr 1)))) (joinEquiv j)=sharedExpected x y (Sum.inr (Sum.inr (Sum.inr 1))) j := by
  simp only [sharedExpected,raw,starHamiltonian,Matrix.one_fin_three]
  rcases j with (j | (j | (j | j))) <;> fin_cases j <;>
    norm_num [sharedHamiltonian,joinEquiv,starCore,Matrix.fromBlocks,Matrix.submatrix,finSumFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

private theorem shared_row7 (x y : ℝ) (j : RawIndex) :
    sharedHamiltonian x y (joinEquiv (Sum.inr (Sum.inr (Sum.inr 2)))) (joinEquiv j)=sharedExpected x y (Sum.inr (Sum.inr (Sum.inr 2))) j := by
  simp only [sharedExpected,raw,starHamiltonian,Matrix.one_fin_three]
  rcases j with (j | (j | (j | j))) <;> fin_cases j <;>
    norm_num [sharedHamiltonian,joinEquiv,starCore,Matrix.fromBlocks,Matrix.submatrix,finSumFinEquiv,
      Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  all_goals rfl

theorem shared_in_raw (x y : ℝ) :
    (sharedHamiltonian x y).submatrix joinEquiv joinEquiv=
      raw (starHamiltonian ((x : ℂ)+y+1) ((x : ℂ)-y))
        (starHamiltonian ((x : ℂ)+y+3) ((x : ℂ)-y)) ((x : ℂ)+y+5) ((x : ℂ)+y-1) := by
  ext i j
  rcases i with (i | (i | (i | i))) <;> fin_cases i
  · exact shared_row0 x y j
  · exact shared_row1 x y j
  · exact shared_row2 x y j
  · exact shared_row3 x y j
  · exact shared_row4 x y j
  · exact shared_row5 x y j
  · exact shared_row6 x y j
  · exact shared_row7 x y j

theorem shared_split (x y : ℝ) : sharedHamiltonian x y=
    splice (starHamiltonian ((x : ℂ)+y+1) ((x : ℂ)-y))
      (starHamiltonian ((x : ℂ)+y+3) ((x : ℂ)-y)) ((x : ℂ)+y+5) ((x : ℂ)+y-1) := by
  have h := congrArg (fun M : Matrix RawIndex RawIndex ℂ => M.submatrix joinEquiv.symm joinEquiv.symm)
    (shared_in_raw x y)
  simp only [Matrix.submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply] at h
  exact h

theorem splice_smul (z : ℂ) (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) :
    z • splice M N a b=splice (z • M) (z • N) (z*a) (z*b) := by
  have scalar (c : ℂ) : z • Matrix.scalar (Fin 1) c=Matrix.scalar (Fin 1) (z*c) := by
    change z • (Matrix.scalarAlgHom (Fin 1) ℂ) c=(Matrix.scalarAlgHom (Fin 1) ℂ) (z • c)
    exact (map_smul _ _ _).symm
  have same : z • raw M N a b=raw (z • M) (z • N) (z*a) (z*b) := by
    simp only [raw,Matrix.fromBlocks_smul,smul_zero,scalar]
  exact congrArg (fun A : Matrix RawIndex RawIndex ℂ => A.submatrix joinEquiv.symm joinEquiv.symm) same

private theorem real_complex_smul {ι : Type*} (M : Matrix ι ι ℂ) (time : ℝ) :
    time • (-Complex.I • M)=((time : ℂ)*(-Complex.I)) • M := by
  ext i j
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,mul_assoc]

theorem splice_flow (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) (time : ℝ) :
    Phase.flowPolynomial (splice M N a b) time=
      splice (Phase.flowPolynomial M time) (Phase.flowPolynomial N time)
        (Primitive.scalarPolynomial (((time : ℂ)*(-Complex.I))*a) 14)
        (Primitive.scalarPolynomial (((time : ℂ)*(-Complex.I))*b) 14) := by
  unfold Phase.flowPolynomial
  simp only [real_complex_smul]
  rw [splice_smul,splice_polynomial]

def sharedValue (x y time : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let z : ℂ := (time : ℂ)*(-Complex.I)
  splice (starAssembly ((x : ℂ)-y) (coefficientPolynomial ((x : ℂ)+y+1) ((x : ℂ)-y) z 14))
    (starAssembly ((x : ℂ)-y) (coefficientPolynomial ((x : ℂ)+y+3) ((x : ℂ)-y) z 14))
    (Primitive.scalarPolynomial (z*((x : ℂ)+y+5)) 14)
    (Primitive.scalarPolynomial (z*((x : ℂ)+y-1)) 14)

theorem shared_flow_values (x y time : ℝ) : Phase.flowPolynomial (sharedHamiltonian x y) time=sharedValue x y time := by
  rw [shared_split,splice_flow]
  simp only [starHamiltonian,original_star_flow,sharedValue]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
