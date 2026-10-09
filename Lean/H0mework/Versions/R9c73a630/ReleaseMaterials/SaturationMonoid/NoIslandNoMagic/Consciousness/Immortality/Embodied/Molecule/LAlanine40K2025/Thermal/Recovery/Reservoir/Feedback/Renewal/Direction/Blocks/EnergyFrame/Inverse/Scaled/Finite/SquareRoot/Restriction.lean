import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private def reindexMorphism {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e.symm with
    map_star' := by intro A; rfl
    map_smul' := by intro c A; rfl }

theorem reindex_sqrt {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (A : Matrix ι ι ℂ) (positive : A.PosSemidef) :
    (CFC.sqrt A).submatrix e e=CFC.sqrt (A.submatrix e e) := by
  let f := reindexMorphism e
  have rootPositive : (f (CFC.sqrt A)).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).submatrix e
  have square : f (CFC.sqrt A)*f (CFC.sqrt A)=f A := by rw [← map_mul,CFC.sqrt_mul_sqrt_self A positive.nonneg]
  exact (CFC.sqrt_unique square rootPositive.nonneg).symm

theorem finite_effect_preserves : Preserves pceOrbit finiteEffect := by
  exact preserves_add (preserves_smul (preserves_one pceOrbit) _) (preserves_smul rational_core_preserves _)

theorem original_finite_root_restriction (a b : Basis) (distinct : a ≠ b) :
    (CFC.sqrt finiteEffect).submatrix (orbitPCE a b) (orbitPCE a b)=
      CFC.sqrt (finiteEffect.submatrix (orbitPCE a b) (orbitPCE a b)) := by
  have positive := Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1
  have same := restrict_sqrt finite_effect_preserves positive s(a,b)
  have renamed := congrArg (fun M => M.submatrix (offDiagonalPCEEquiv a b distinct) (offDiagonalPCEEquiv a b distinct)) same
  rw [reindex_sqrt (offDiagonalPCEEquiv a b distinct) (restrict pceOrbit s(a,b) finiteEffect) (positive.submatrix Subtype.val)] at renamed
  exact renamed

theorem original_finite_complement_restriction (a b : Basis) (distinct : a ≠ b) :
    (CFC.sqrt (1-finiteEffect)).submatrix (orbitPCE a b) (orbitPCE a b)=
      CFC.sqrt ((1-finiteEffect).submatrix (orbitPCE a b) (orbitPCE a b)) := by
  have positive := Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2
  have same := restrict_sqrt (preserves_sub (preserves_one pceOrbit) finite_effect_preserves) positive s(a,b)
  have renamed := congrArg (fun M => M.submatrix (offDiagonalPCEEquiv a b distinct) (offDiagonalPCEEquiv a b distinct)) same
  rw [reindex_sqrt (offDiagonalPCEEquiv a b distinct) (restrict pceOrbit s(a,b) (1-finiteEffect)) (positive.submatrix Subtype.val)] at renamed
  exact renamed

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
