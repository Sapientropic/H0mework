import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCAlgebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open scoped Matrix BigOperators
noncomputable section

abbrev RawIndex := Fin 3 ⊕ (Fin 1 ⊕ (Fin 1 ⊕ Fin 3))

def joinEquiv : RawIndex ≃ Fin 8 :=
  (Equiv.sumCongr (Equiv.refl (Fin 3))
    ((Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4)).trans
      (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5))).trans finSumFinEquiv

def raw (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) : Matrix RawIndex RawIndex ℂ :=
  Matrix.fromBlocks M 0 0
    (Matrix.fromBlocks (Matrix.scalar (Fin 1) a) 0 0
      (Matrix.fromBlocks (Matrix.scalar (Fin 1) b) 0 0 N))

def splice (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  (raw M N a b).submatrix joinEquiv.symm joinEquiv.symm

theorem join_sum {ι κ ν : Type*} (S : Finset ν)
    (A : ν → Matrix ι ι ℂ) (B : ν → Matrix κ κ ℂ) :
    (∑ n ∈ S, Matrix.fromBlocks (A n) 0 0 (B n))=
      Matrix.fromBlocks (∑ n ∈ S,A n) 0 0 (∑ n ∈ S,B n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S absent ih => simp only [Finset.sum_insert absent,ih,Matrix.fromBlocks_add,add_zero]

theorem join_polynomial {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℂ) (N : Matrix κ κ ℂ) (n : Nat) :
    Phase.polynomial (Matrix.fromBlocks M 0 0 N) n=
      Matrix.fromBlocks (Phase.polynomial M n) 0 0 (Phase.polynomial N n) := by
  simp only [Phase.polynomial,Matrix.fromBlocks_diagonal_pow,Matrix.fromBlocks_smul,smul_zero]
  exact join_sum _ _ _

theorem scalar_polynomial (a : ℂ) (n : Nat) :
    Phase.polynomial (Matrix.scalar (Fin 1) a) n=Matrix.scalar (Fin 1) (Primitive.scalarPolynomial a n) := by
  let f : ℂ →ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ := Matrix.scalarAlgHom (Fin 1) ℂ
  change (∑ k ∈ Finset.range n,(k.factorial : ℂ)⁻¹ • (f a)^k)=
    f (∑ k ∈ Finset.range n,(k.factorial : ℂ)⁻¹ • a^k)
  simp only [map_sum,map_smul,map_pow]

theorem raw_polynomial (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) (n : Nat) :
    Phase.polynomial (raw M N a b) n=
      raw (Phase.polynomial M n) (Phase.polynomial N n)
        (Primitive.scalarPolynomial a n) (Primitive.scalarPolynomial b n) := by
  simp only [raw,join_polynomial,scalar_polynomial]

theorem splice_polynomial (M N : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ) (n : Nat) :
    Phase.polynomial (splice M N a b) n=
      splice (Phase.polynomial M n) (Phase.polynomial N n)
        (Primitive.scalarPolynomial a n) (Primitive.scalarPolynomial b n) := by
  rw [splice,← Primitive.polynomial_reindex,raw_polynomial]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
