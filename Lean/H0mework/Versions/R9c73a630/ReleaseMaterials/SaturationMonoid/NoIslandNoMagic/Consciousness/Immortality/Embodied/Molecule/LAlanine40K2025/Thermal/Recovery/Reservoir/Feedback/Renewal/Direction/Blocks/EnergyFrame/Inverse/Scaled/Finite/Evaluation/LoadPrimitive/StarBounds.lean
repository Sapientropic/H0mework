import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.SourceValues
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem source_delta_norm (a b : Basis) : ‖(sourceDelta a b : ℂ)‖ ≤ 38 := by
  have bounded (i : Basis) : ‖(Diagonal.energy i : ℂ)‖ ≤ 19 := by
    rw [Diagonal.energy_original]
    exact (Load.Producer.StrictThermal.matrix_entry_norm_le E i i).trans diagonal_norm
  rw [sourceDelta,Rat.cast_sub]
  exact (norm_sub_le _ _).trans ((add_le_add (bounded a) (bounded b)).trans (by norm_num))

theorem star_core_norm (d : ℂ) (bounded : ‖d‖ ≤ 38) : ‖starCore d‖ ≤ 80 := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by norm_num)
  norm_num [starCore,Fin.sum_univ_succ]
  nlinarith [norm_nonneg d]

theorem star_power_norm (d : ℂ) (bounded : ‖d‖ ≤ 38) : ‖(starCore d)^2‖ ≤ 6400 :=
  (norm_pow_le _ _).trans ((pow_le_pow_left₀ (norm_nonneg _) (star_core_norm d bounded) 2).trans (by norm_num))

theorem star_error (d : ℂ) (bounded : ‖d‖ ≤ 38) (f g : Fin 3 → ℂ)
    (zero : ‖f 0-g 0‖ ≤ (1/10^24 : ℝ))
    (one : ‖f 1-g 1‖ ≤ (1/10^30 : ℝ))
    (two : ‖f 2-g 2‖ ≤ (1/10^30 : ℝ)) :
    ‖starAssembly d f-starAssembly d g‖ ≤ (2/10^24 : ℝ) := by
  rw [starAssembly,starAssembly,← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  simp only [← sub_smul,norm_smul,Fin.sum_univ_succ,starBasis,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,norm_one,add_zero,mul_one]
  change ‖f 0-g 0‖+(‖f 1-g 1‖*‖starCore d‖+‖f 2-g 2‖*‖(starCore d)^2‖) ≤ (2/10^24 : ℝ)
  have first := mul_le_mul one (star_core_norm d bounded) (norm_nonneg _) (by norm_num)
  have second := mul_le_mul two (star_power_norm d bounded) (norm_nonneg _) (by norm_num)
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
