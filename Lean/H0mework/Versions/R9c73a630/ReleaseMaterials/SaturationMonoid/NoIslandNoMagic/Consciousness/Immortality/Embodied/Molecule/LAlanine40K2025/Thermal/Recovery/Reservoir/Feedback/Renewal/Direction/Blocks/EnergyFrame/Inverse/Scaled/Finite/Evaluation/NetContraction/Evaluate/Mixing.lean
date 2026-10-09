import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Roles

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed Contraction
open scoped Matrix

variable {α β : Type*}

def roleMixQ (c s : ℚ) (A : MatrixQ (Leg α β) (Leg α β)) : MatrixQ (Role α β) (Role α β)
  | (.inl i,e),(.inl j,f) => Scalar.multiply (c,0) (A (i,e) (j,f))
  | (.inr i,e),(.inr j,f) => Scalar.multiply (c,0) (A (i,e) (j,f))
  | (.inl i,e),(.inr j,f) => Scalar.multiply (0,-s) (A (i,e) (j,f))
  | (.inr i,e),(.inl j,f) => Scalar.multiply (0,-s) (A (i,e) (j,f))

private theorem scalar_zero_left (a : Scalar.QComplex) : Scalar.multiply (0,0) a=(0,0) := by simp [Scalar.multiply]
private theorem scalar_zero_right (a : Scalar.QComplex) : Scalar.multiply a (0,0)=(0,0) := by simp [Scalar.multiply]

set_option linter.unusedSimpArgs false in
theorem mixing_role_restriction (f : α → PairController) (g : β → PairController)
    (k l : Sym2 Basis) (different : k ≠ l) (fk : ∀ i, pcOrbit (f i)=k) (gl : ∀ i, pcOrbit (g i)=l)
    (U : MatrixQ PairController PairController) (E : MatrixQ (Fin 2) (Fin 2)) (c s : ℚ)
    (kept : Preserves pcOrbit (qvalue U)) :
    (qkron (qscale (c,0) (qkron U U)+qscale (0,-s) ((qkron U U).submatrix id Prod.swap)) E).submatrix
        (roleAddress f g) (roleAddress f g)=
      roleMixQ c s (qkron (qkron (U.submatrix f f) (U.submatrix g g)) E) := by
  have fg (a : α) (b : β) : U (f a) (g b)=(0,0) :=
    qpc_zero_of_separated U kept _ _ (by rw [fk,gl]; exact different)
  have gf (b : β) (a : α) : U (g b) (f a)=(0,0) :=
    qpc_zero_of_separated U kept _ _ (by rw [fk,gl]; exact different.symm)
  funext ⟨x,e⟩ ⟨y,t⟩
  rcases x with (x | x) <;> rcases y with (y | y)
  all_goals
    simp only [roleMixQ,roleAddress,Matrix.submatrix_apply,qscale,qkron,Matrix.add_apply,
      Prod.swap_prod_mk,id_eq,fg,gf,scalar_zero_left,scalar_zero_right,add_zero,zero_add]
    apply Prod.ext <;> simp only [Scalar.multiply,Prod.fst_add,Prod.snd_add] <;> ring

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
