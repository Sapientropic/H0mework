import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Gap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_gap (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) (tau mu : ℝ)
    (positive : 0 < tau) (upper : ‖A‖ ≤ mu) :
    (tau/(2*(tau+mu))) • (1 : Matrix ι ι ℂ) ≤ normalizedAt tau mu A := by
  have lower := hermitian.isSelfAdjoint.neg_algebraMap_norm_le_self
  rw [Algebra.algebraMap_eq_smul_one] at lower
  have compare := smul_le_smul_of_nonneg_right upper (zero_le_one : (0 : Matrix ι ι ℂ) ≤ 1)
  have shifted : 0 ≤ mu • (1 : Matrix ι ι ℂ)+A := (neg_le_iff_add_nonneg').mp ((neg_le_neg compare).trans lower)
  have den : 0 < tau+mu := by linarith [norm_nonneg A]
  have expression : normalizedAt tau mu A-(tau/(2*(tau+mu))) • (1 : Matrix ι ι ℂ)=
      (1/(2*(tau+mu)) : ℝ) • (mu • (1 : Matrix ι ι ℂ)+A) := by
    ext i j
    simp only [normalizedAt,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
    push_cast
    have complexDen : (tau : ℂ)+(mu : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt den
    field_simp [complexDen]
    ring
  apply sub_nonneg.mp
  rw [expression]
  exact smul_nonneg (by positivity) shifted

theorem finite_gap_scalar : (1/10^10 : ℝ) ≤ rationalRegularizer/(2*(rationalRegularizer+480362644764/10^10)) := by
  unfold rationalRegularizer
  rw [cosine_hat_exact]
  norm_num

theorem finite_both_gap : (1/10^10 : ℝ) • (1 : LoadedJoint) ≤ finiteEffect ∧
    (1/10^10 : ℝ) • (1 : LoadedJoint) ≤ 1-finiteEffect := by
  have increase := smul_le_smul_of_nonneg_right finite_gap_scalar (zero_le_one : (0 : LoadedJoint) ≤ 1)
  constructor
  · exact increase.trans (normalized_gap rationalCore rational_core_hermitian rationalRegularizer _ rational_regularizer_positive original_rational_norm_interval.2)
  · change (1/10^10 : ℝ) • (1 : LoadedJoint) ≤ 1-normalizedAt rationalRegularizer (480362644764/10^10) rationalCore
    rw [normalized_complement]
    exact increase.trans (normalized_gap (-rationalCore) rational_core_hermitian.neg rationalRegularizer _ rational_regularizer_positive (by simpa only [norm_neg] using original_rational_norm_interval.2))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
