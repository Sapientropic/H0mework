import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.DiagonalSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Complex

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem active_value_integer (i : Basis) :
    Scalar.value (Diagonal.activeValue i)=((activeRe i : ℂ)+Complex.I*(activeIm i : ℂ))/(10^24 : ℂ) := by
  rw [← active_source i]
  simp only [Scalar.value,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat]
  ring

theorem original_active_integer : Diagonal.activeMatrix=
    scaledMatrix (Matrix.diagonal activeRe) (Matrix.diagonal activeIm) (10^24) := by
  ext i j
  rw [Diagonal.activeMatrix,scaledMatrix_entry]
  by_cases same : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Int.cast_pow,Int.cast_ofNat]
    exact active_value_integer i
  · simp only [Matrix.diagonal_apply,if_neg same,Int.cast_zero,mul_zero,zero_add,zero_div]

theorem gibbs_mass_integer : Diagonal.gibbsMass=(gibbsTotal : ℚ)/(10^24 : ℚ) := by
  simp only [Diagonal.gibbsMass,gibbsTotal,Int.cast_sum,Finset.sum_div,gibbs_source]

theorem gibbs_quotient (i : Basis) : (Diagonal.gibbsValue i).1/Diagonal.gibbsMass=(gibbsInt i : ℚ)/(gibbsTotal : ℚ) := by
  rw [← gibbs_source i,gibbs_mass_integer]
  have nz : (gibbsTotal : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt gibbs_total_positive)
  field_simp

theorem original_gibbs_integer : Diagonal.computedGibbs=
    scaledMatrix (Matrix.diagonal gibbsInt) 0 gibbsTotal := by
  ext i j
  rw [Diagonal.computedGibbs,scaledMatrix_entry]
  by_cases same : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.zero_apply,Int.cast_zero,mul_zero,add_zero,gibbs_quotient,Rat.cast_div,Rat.cast_intCast]
  · simp only [Matrix.diagonal_apply,if_neg same,Matrix.zero_apply,Int.cast_zero,mul_zero,zero_add,zero_div]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
