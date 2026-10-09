import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Roles

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
open Propagation.Interface Load.Source Fixed Contraction
open scoped Matrix

variable {α β : Type*}

theorem local_role_restriction (f : α → PairController) (g : β → PairController)
    (k l : Sym2 Basis) (different : k ≠ l) (fk : ∀ i, pcOrbit (f i)=k) (gl : ∀ i, pcOrbit (g i)=l)
    (U : MatrixQ (PairController × Fin 2) (PairController × Fin 2)) (V : MatrixQ PairController PairController)
    (kept : Preserves pceOrbit (qvalue U)) :
    (localMatrixQ U V).submatrix (roleAddress f g) (roleAddress f g)=
      roleBlocksQ (bodyLiftQ (U.submatrix (liftedAddress f) (liftedAddress f)) (V.submatrix g g))
        (donorLiftQ (U.submatrix (liftedAddress g) (liftedAddress g)) (V.submatrix f f)) := by
  funext ⟨x,e⟩ ⟨y,t⟩
  rcases x with (x | x) <;> rcases y with (y | y)
  · rfl
  · change Scalar.multiply (U (f x.1,e) (g y.2,t)) (V (g x.2) (f y.1))=(0,0)
    have separate : pceOrbit (f x.1,e) ≠ pceOrbit (g y.2,t) := by
      change pcOrbit (f x.1) ≠ pcOrbit (g y.2)
      rw [fk,gl]
      exact different
    rw [qzero_of_separated U kept _ _ separate]
    simp [Scalar.multiply]
  · change Scalar.multiply (U (g x.2,e) (f y.1,t)) (V (f x.1) (g y.2))=(0,0)
    have separate : pceOrbit (g x.2,e) ≠ pceOrbit (f y.1,t) := by
      change pcOrbit (g x.2) ≠ pcOrbit (f y.1)
      rw [fk,gl]
      exact different.symm
    rw [qzero_of_separated U kept _ _ separate]
    simp [Scalar.multiply]
  · exact scalar_multiply_comm _ _

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
