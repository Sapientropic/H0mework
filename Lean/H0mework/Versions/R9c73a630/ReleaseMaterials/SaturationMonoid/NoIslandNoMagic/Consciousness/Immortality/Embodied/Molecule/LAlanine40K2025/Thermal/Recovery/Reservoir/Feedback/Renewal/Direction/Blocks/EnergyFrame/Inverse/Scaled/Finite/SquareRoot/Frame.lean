import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Original

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Propagation.Interface Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def originalFrameEffect : LoadedJoint := Quantum.conjugation (star installedLoadFrame) (Quantum.conjugation numericFree finiteEffect)

theorem original_frame_lawful : originalFrameEffect.PosSemidef ∧ (1-originalFrameEffect).PosSemidef := by
  constructor
  · exact Quantum.conjugation_posSemidef (star installedLoadFrame) _
      (Quantum.conjugation_posSemidef numericFree _ (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1))
  · change (1-Quantum.conjugation (star installedLoadFrame) (Quantum.conjugation numericFree finiteEffect)).PosSemidef
    rw [← conjugated_complement,← conjugated_complement]
    exact Quantum.conjugation_posSemidef (star installedLoadFrame) _
      (Quantum.conjugation_posSemidef numericFree _ (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2))

theorem frame_undo (A : LoadedJoint) : Quantum.conjugation installedLoadFrame
    (Quantum.conjugation (star installedLoadFrame) A)=A := by
  rw [Environment.conjugation_comp]
  simp only [Unitary.mul_star_self,Quantum.conjugation_apply,Submonoid.coe_one,star_one,Matrix.one_mul,Matrix.mul_one]

theorem original_frame_root_identity : Quantum.conjugation installedLoadFrame (effectRoot originalFrameEffect)=
    Quantum.conjugation numericFree (effectRoot finiteEffect) := by
  rw [effectRoot,sqrt_conjugation installedLoadFrame originalFrameEffect original_frame_lawful.1]
  change CFC.sqrt (Quantum.conjugation installedLoadFrame (Quantum.conjugation (star installedLoadFrame) (Quantum.conjugation numericFree finiteEffect)))=_
  rw [frame_undo,← sqrt_conjugation numericFree finiteEffect (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1)]
  rfl

theorem original_frame_complement_identity : Quantum.conjugation installedLoadFrame (complementRoot originalFrameEffect)=
    Quantum.conjugation numericFree (complementRoot finiteEffect) := by
  rw [complementRoot,sqrt_conjugation installedLoadFrame (1-originalFrameEffect) original_frame_lawful.2,
    conjugated_complement]
  change CFC.sqrt (1-Quantum.conjugation installedLoadFrame (Quantum.conjugation (star installedLoadFrame) (Quantum.conjugation numericFree finiteEffect)))=_
  rw [frame_undo,← conjugated_complement,← sqrt_conjugation numericFree (1-finiteEffect) (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2)]
  rfl

theorem original_frame_root_error : ‖effectRoot (sourceMeasurementEffect loadTotalHamiltonian)-effectRoot originalFrameEffect‖ ≤ (14/10^6 : ℝ) := by
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame)
    (effectRoot (sourceMeasurementEffect loadTotalHamiltonian)-effectRoot originalFrameEffect)
  change ‖Quantum.conjugation installedLoadFrame (effectRoot (sourceMeasurementEffect loadTotalHamiltonian)-effectRoot originalFrameEffect)‖=_ at same
  rw [← same,map_sub,original_effect_root_calculated,original_frame_root_identity]
  exact calculated_finite_root_error

theorem original_frame_complement_error : ‖complementRoot (sourceMeasurementEffect loadTotalHamiltonian)-complementRoot originalFrameEffect‖ ≤ (14/10^6 : ℝ) := by
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame)
    (complementRoot (sourceMeasurementEffect loadTotalHamiltonian)-complementRoot originalFrameEffect)
  change ‖Quantum.conjugation installedLoadFrame (complementRoot (sourceMeasurementEffect loadTotalHamiltonian)-complementRoot originalFrameEffect)‖=_ at same
  rw [← same,map_sub,original_complement_root_calculated,original_frame_complement_identity]
  exact calculated_finite_complement_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
