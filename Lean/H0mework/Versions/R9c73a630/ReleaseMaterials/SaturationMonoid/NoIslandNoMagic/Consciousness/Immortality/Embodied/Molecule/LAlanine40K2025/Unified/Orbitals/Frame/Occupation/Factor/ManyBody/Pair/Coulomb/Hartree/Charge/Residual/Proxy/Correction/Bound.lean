import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.Algebra
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Consumers
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.First.Assembly

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel OriginalMetric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
noncomputable section

private theorem correction_inverse_root :
    actualCorrection * CFC.sqrt actualGram = 1 := by
  have unit : IsUnit (CFC.sqrt actualGram) :=
    (CFC.isUnit_sqrt_iff actualGram actual_gram_positive.posSemidef.nonneg).mpr
      actual_gram_positive.isUnit
  let := unit.invertible
  simp [actualCorrection,metricCorrection]

theorem complex_correction_inverse_root :
    complexMatrix actualCorrection * complexMatrix (CFC.sqrt actualGram) = 1 := by
  rw [← complexMatrix_mul,correction_inverse_root,complexMatrix_one]

theorem correction_complex_norm_error :
    ‖complexMatrix actualCorrection - 1‖ ≤ (392 / 10^9 : ℝ) := by
  let C : Matrix Basis Basis ℂ := complexMatrix actualCorrection
  let B : Matrix Basis Basis ℂ := complexMatrix (CFC.sqrt actualGram)
  let ε : ℝ := 196 / 10^9
  have rootError : ‖B - 1‖ ≤ ε :=
    (source_root_error actual_gram_positive).trans actual_gram_norm_error
  have inverseProduct : C * B = 1 := complex_correction_inverse_root
  have factor : C - 1 = C * (1 - B) := by
    rw [Matrix.mul_sub,Matrix.mul_one,inverseProduct]
  have errorLe : ‖C - 1‖ ≤ ‖C‖ * ε := by
    rw [factor]
    calc
      _ ≤ ‖C‖ * ‖1 - B‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖C‖ * ε := by rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left rootError (norm_nonneg _)
  have normLe : ‖C‖ ≤ ‖C - 1‖ + 1 := by
    calc
      _ = ‖(C - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖C - 1‖ + ‖(1 : Matrix Basis Basis ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_one]
  have nonnegative : 0 ≤ ‖C‖ := norm_nonneg _
  have two : ‖C‖ ≤ 2 := by
    dsimp [ε] at errorLe
    nlinarith
  change ‖C - 1‖ ≤ _
  dsimp [ε] at errorLe
  nlinarith

theorem first_defect_entry_error (i j : Basis) :
    |firstDefect i j| ≤ (4 / 10^11 : ℝ) := by
  rw [first_defect_source,Matrix.mul_apply]
  have h (k : Basis) :
      |(originalMetric - realRecorded) i k * realInverse k j| ≤
        (1 / 10^12 : ℝ) * |realInverse k j| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [originalMetric,realRecorded,Matrix.sub_apply,Matrix.of_apply,
          realInverse,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
        using original_overlap_error i k)
      (abs_nonneg _)
  calc
    |∑ k : Basis, (originalMetric - realRecorded) i k * realInverse k j| ≤
        ∑ k : Basis, |(originalMetric - realRecorded) i k * realInverse k j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Basis, (1 / 10^12 : ℝ) * |realInverse k j| :=
      Finset.sum_le_sum (fun k _ => h k)
    _ = (1 / 10^12 : ℝ) * (columnSize j : ℝ) := by
      rw [← Finset.mul_sum]
      simp only [columnSize,realInverse,Rat.cast_sum,Rat.cast_abs]
    _ ≤ (1 / 10^12 : ℝ) * 40 := by
      gcongr
      exact_mod_cast First.columnSize_bound j
    _ = _ := by norm_num

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
