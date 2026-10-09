import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ScalarMaterial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCNorm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Propagation.Producer
open scoped Matrix Matrix.Norms.L2Operator

abbrev PCMaterial (a b : Basis) := ∀ n : Fin 4, ScalarMaterial (scalarEnergy a b n)

noncomputable def materialPCOne (a b : Basis) (M : PCMaterial a b) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (pcAssembly (fun n => Scalar.value (M n).one)).submatrix finProdFinEquiv finProdFinEquiv

noncomputable def materialPCTwo (a b : Basis) (M : PCMaterial a b) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (pcAssembly (fun n => Scalar.value (M n).two)).submatrix finProdFinEquiv finProdFinEquiv

private theorem difference_reindex_norm {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (A B : Matrix ι ι ℂ) :
    ‖A.submatrix e e-B.submatrix e e‖=‖A-B‖ := by
  have same : A.submatrix e e-B.submatrix e e=(A-B).submatrix e e := rfl
  rw [same,Finite.reindex_norm]

attribute [local irreducible] ordinaryPCValues Scalar.value Scalar.polynomial scalarSeed scalarEnergy

theorem material_pc_one_error (a b : Basis) (distinct : a ≠ b) (M : PCMaterial a b) :
    ‖Phase.pcPolynomial.submatrix (orbitPC a b) (orbitPC a b)-materialPCOne a b M‖ ≤ (4/10^24 : ℝ) := by
  rw [original_free_pc_shared a b distinct]
  have bound : ‖pcAssembly (ordinaryPCValues a b (nativeClockStep : ℝ))-pcAssembly (fun n => Scalar.value (M n).one)‖ ≤ (4/10^24 : ℝ) := by
    apply (pc_assembly_error _ _ (1/10^24) (by norm_num) ?_).trans (by norm_num)
    intro n
    have p := material_one_error _ (M n)
    rw [original_scalar_polynomial a b n 1] at p
    norm_num only [Rat.cast_one,one_mul] at p
    exact p.trans (by norm_num)
  unfold sharedOrdinaryPC materialPCOne
  exact (difference_reindex_norm (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) _ _).le.trans bound

theorem material_pc_two_error (a b : Basis) (distinct : a ≠ b) (M : PCMaterial a b) :
    ‖Actions.parentPCPolynomial.submatrix (orbitPC a b) (orbitPC a b)-materialPCTwo a b M‖ ≤ (4/10^24 : ℝ) := by
  rw [original_parent_pc_shared a b distinct]
  have bound : ‖pcAssembly (ordinaryPCValues a b (2*(nativeClockStep : ℝ)))-pcAssembly (fun n => Scalar.value (M n).two)‖ ≤ (4/10^24 : ℝ) := by
    apply (pc_assembly_error _ _ (1/10^24) (by norm_num) ?_).trans (by norm_num)
    intro n
    have p := material_two_error _ (M n)
    rw [original_scalar_polynomial a b n 2] at p
    norm_num only [Rat.cast_ofNat] at p
    exact p.trans (by norm_num)
  unfold sharedOrdinaryPC materialPCTwo
  exact (difference_reindex_norm (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) _ _).le.trans bound

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
