import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Gap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem roots_of_paid_effect (A B : LoadedJoint) (ha : A.IsHermitian) (hb : B.IsHermitian)
    (gapA : (1/10^10 : ℝ) ≤ effectGap A) (gapB : (1/10^10 : ℝ) ≤ effectGap B)
    (paid : ‖boundedEffect A-boundedEffect B‖ ≤ (261/10^12 : ℝ)) :
    ‖effectRoot (boundedEffect A)-effectRoot (boundedEffect B)‖ ≤ (14/10^6 : ℝ) := by
  have floorA : ((1/10^5 : ℝ)*(1/10^5)) • (1 : LoadedJoint) ≤ boundedEffect A := by
    convert (smul_le_smul_of_nonneg_right gapA zero_le_one).trans (bounded_effect_gap A ha) using 1
    norm_num
  have floorB : ((1/10^5 : ℝ)*(1/10^5)) • (1 : LoadedJoint) ≤ boundedEffect B := by
    convert (smul_le_smul_of_nonneg_right gapB zero_le_one).trans (bounded_effect_gap B hb) using 1
    norm_num
  exact sqrt_perturbation _ _ (boundedEffect_positive A ha).nonneg (boundedEffect_positive B hb).nonneg
    (1/10^5) (14/10^6) (by norm_num) (by norm_num) floorA floorB (by linarith)

theorem original_numeric_root_error :
    ‖effectRoot (sourceMeasurementEffect loadTotalHamiltonian)-
      effectRoot (boundedEffect originalFrameNumericOutput)‖ ≤ (14/10^6 : ℝ) :=
  roots_of_paid_effect _ _ (sourceOutputObservable_hermitian _ loadTotalHamiltonian_hermitian)
    original_frame_numeric_hermitian original_both_gap.1 original_both_gap.2 source_frame_effect_error

theorem original_numeric_complement_error :
    ‖complementRoot (sourceMeasurementEffect loadTotalHamiltonian)-
      complementRoot (boundedEffect originalFrameNumericOutput)‖ ≤ (14/10^6 : ℝ) := by
  have ha := sourceOutputObservable_hermitian _ loadTotalHamiltonian_hermitian
  have h := roots_of_paid_effect (-(sourceOutputObservable loadTotalHamiltonian)) (-originalFrameNumericOutput)
    ha.neg original_frame_numeric_hermitian.neg
    (by simpa only [effectGap,measurementScale,norm_neg] using original_both_gap.1)
    (by simpa only [effectGap,measurementScale,norm_neg] using original_both_gap.2)
    (by simpa only [sourceMeasurementEffect,← boundedEffect_complement,sub_sub_sub_cancel_left,norm_sub_rev] using source_frame_effect_error)
  simpa only [sourceMeasurementEffect,effectRoot,complementRoot,← boundedEffect_complement] using h

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
