import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Instrument

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def effectGap (A : Matrix ι ι ℂ) : ℝ := (2*measurementScale A)⁻¹

theorem effect_gap_positive (A : Matrix ι ι ℂ) : 0 < effectGap A := by
  unfold effectGap
  exact inv_pos.mpr (mul_pos (by norm_num) (measurementScale_pos A))

theorem bounded_effect_gap (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) :
    effectGap A • (1 : Matrix ι ι ℂ) ≤ boundedEffect A := by
  have shifted : (0 : Matrix ι ι ℂ) ≤ ‖A‖ • 1+A := by
    have h := hermitian.isSelfAdjoint.neg_algebraMap_norm_le_self
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact (neg_le_iff_add_nonneg').mp h
  have scaled := smul_nonneg (effect_gap_positive A).le shifted
  have expression : effectGap A • (‖A‖ • (1 : Matrix ι ι ℂ)+A) =
      boundedEffect A-effectGap A • (1 : Matrix ι ι ℂ) := by
    have nonzero := (measurementScale_pos A).ne'
    ext i j
    simp only [effectGap,boundedEffect,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,
      smul_eq_mul,Complex.real_smul,measurementScale]
    push_cast
    field_simp
    ring
  rw [expression] at scaled
  exact sub_nonneg.mp scaled

theorem bounded_complement_gap (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) :
    effectGap A • (1 : Matrix ι ι ℂ) ≤ 1-boundedEffect A := by
  rw [boundedEffect_complement]
  have h := bounded_effect_gap (-A) hermitian.neg
  simpa only [effectGap,measurementScale,norm_neg] using h

theorem original_calculated_effect_gap :
    effectGap originalCalculatedOutput • (1 : Load.Source.LoadedJoint) ≤ boundedEffect originalCalculatedOutput ∧
    effectGap originalCalculatedOutput • (1 : Load.Source.LoadedJoint) ≤ 1-boundedEffect originalCalculatedOutput :=
  ⟨bounded_effect_gap _ original_calculated_hermitian,bounded_complement_gap _ original_calculated_hermitian⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
