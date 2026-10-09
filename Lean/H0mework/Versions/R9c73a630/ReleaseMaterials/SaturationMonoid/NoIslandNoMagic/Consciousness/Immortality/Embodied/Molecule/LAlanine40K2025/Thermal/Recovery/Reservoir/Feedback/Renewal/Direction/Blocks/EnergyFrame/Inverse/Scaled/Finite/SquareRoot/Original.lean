import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Gap
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.RootError

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Propagation.Interface Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conjugated_gap (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (d : ℝ)
    (gap : d • (1 : Matrix ι ι ℂ) ≤ A) : d • (1 : Matrix ι ι ℂ) ≤ Quantum.conjugation U A := by
  have p := (Quantum.conjugation_posSemidef U (A-d • (1 : Matrix ι ι ℂ))
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr gap))).nonneg
  have scalar : Quantum.conjugation U (d • (1 : Matrix ι ι ℂ))=d • (1 : Matrix ι ι ℂ) := by
    have same : d • (1 : Matrix ι ι ℂ)=(d : ℂ) • (1 : Matrix ι ι ℂ) := by
      ext i j
      simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
    have one : Quantum.conjugation U (1 : Matrix ι ι ℂ)=1 := map_one (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U)
    rw [same,map_smul,one]
  rw [map_sub,scalar] at p
  exact sub_nonneg.mp p

theorem conjugated_complement (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    Quantum.conjugation U (1-A)=1-Quantum.conjugation U A := by
  have one : Quantum.conjugation U (1 : Matrix ι ι ℂ)=1 := map_one (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U)
  rw [map_sub,one]

theorem roots_from_paid_gap (A B : Matrix ι ι ℂ) (pa : 0 ≤ A) (pb : 0 ≤ B)
    (ga : (1/10^10 : ℝ) • (1 : Matrix ι ι ℂ) ≤ A)
    (gb : (1/10^10 : ℝ) • (1 : Matrix ι ι ℂ) ≤ B)
    (paid : ‖A-B‖ ≤ (266/10^12 : ℝ)) : ‖CFC.sqrt A-CFC.sqrt B‖ ≤ (14/10^6 : ℝ) := by
  apply sqrt_perturbation A B pa pb (1/10^5) (14/10^6) (by norm_num) (by norm_num)
  · convert ga using 1
    norm_num
  · convert gb using 1
    norm_num
  · linarith

theorem calculated_finite_root_error :
    ‖effectRoot (boundedEffect originalCalculatedOutput)-Quantum.conjugation numericFree (effectRoot finiteEffect)‖ ≤ (14/10^6 : ℝ) := by
  have ha := boundedEffect_positive originalCalculatedOutput original_calculated_hermitian
  have hb := Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1
  have ga : (1/10^10 : ℝ) ≤ effectGap originalCalculatedOutput := by
    simpa only [effectGap,original_scale_calculated] using original_both_gap.1
  have floorA := (smul_le_smul_of_nonneg_right ga (zero_le_one : (0 : LoadedJoint) ≤ 1)).trans
    (bounded_effect_gap originalCalculatedOutput original_calculated_hermitian)
  have paid := source_finite_effect_error
  rw [original_effect_calculated] at paid
  have step := roots_from_paid_gap _ _ ha.nonneg (Quantum.conjugation_posSemidef numericFree finiteEffect hb).nonneg
    floorA (conjugated_gap numericFree finiteEffect _ finite_both_gap.1) paid
  simpa only [effectRoot,← sqrt_conjugation numericFree finiteEffect hb] using step

theorem calculated_finite_complement_error :
    ‖complementRoot (boundedEffect originalCalculatedOutput)-Quantum.conjugation numericFree (complementRoot finiteEffect)‖ ≤ (14/10^6 : ℝ) := by
  have ha := boundedEffect_complement_positive originalCalculatedOutput original_calculated_hermitian
  have hb := Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2
  have ga : (1/10^10 : ℝ) ≤ effectGap originalCalculatedOutput := by
    simpa only [effectGap,original_scale_calculated] using original_both_gap.1
  have floorA := (smul_le_smul_of_nonneg_right ga (zero_le_one : (0 : LoadedJoint) ≤ 1)).trans
    (bounded_complement_gap originalCalculatedOutput original_calculated_hermitian)
  have paid : ‖(1-boundedEffect originalCalculatedOutput)-Quantum.conjugation numericFree (1-finiteEffect)‖ ≤ (266/10^12 : ℝ) := by
    rw [conjugated_complement,sub_sub_sub_cancel_left,norm_sub_rev]
    have h := source_finite_effect_error
    rwa [original_effect_calculated] at h
  have step := roots_from_paid_gap _ _ ha.nonneg (Quantum.conjugation_posSemidef numericFree (1-finiteEffect) hb).nonneg
    floorA (conjugated_gap numericFree (1-finiteEffect) _ finite_both_gap.2) paid
  simpa only [complementRoot,← sqrt_conjugation numericFree (1-finiteEffect) hb] using step

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
