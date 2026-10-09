import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Sectors.Orbit

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
open Collision Propagation.Interface Load.Source
open scoped Matrix ComplexOrder
noncomputable section

theorem original_effect_preserves : Preserves reservoirOrbit sourceEffect :=
  bodyObservable_preserves _ Spectral.Current.effect_preserves

theorem fromBlocks_preserves (A B C D : Current.FullJoint)
    (a : Preserves reservoirOrbit A) (b : Preserves reservoirOrbit B)
    (c : Preserves reservoirOrbit C) (d : Preserves reservoirOrbit D) :
    Preserves pointerOrbit (Matrix.fromBlocks A B C D) := by
  intro i j separated
  cases i with
  | inl i =>
    cases j with
    | inl j => exact a i j separated
    | inr j => exact b i j separated
  | inr i =>
    cases j with
    | inl j => exact c i j separated
    | inr j => exact d i j separated

theorem original_dilation_preserves : Preserves pointerOrbit (sourceUnitary : PointerJoint) :=
  fromBlocks_preserves _ _ _ _ (preserves_sqrt original_effect_preserves)
    (preserves_neg (preserves_sqrt (preserves_sub (preserves_one _) original_effect_preserves)))
    (preserves_sqrt (preserves_sub (preserves_one _) original_effect_preserves))
    (preserves_sqrt original_effect_preserves)

theorem controlled_preserves (U V : Matrix.unitaryGroup Current.FullIndex ℂ)
    (left : Preserves reservoirOrbit (U : Current.FullJoint))
    (right : Preserves reservoirOrbit (V : Current.FullJoint)) :
    Preserves pointerOrbit (blockUnitary U V : PointerJoint) :=
  fromBlocks_preserves _ _ _ _ left (preserves_zero _) (preserves_zero _) right

theorem feedback_preserves (time : ℝ) :
    Preserves pointerOrbit (feedbackPulse time : PointerJoint) :=
  controlled_preserves _ _ (original_load_preserves time)
    (preserves_smul (original_pulse_preserves time) (freePhase time : ℂ))

theorem pointer_load_preserves (time : ℝ) :
    Preserves pointerOrbit (Pointer.loadPulse time : PointerJoint) :=
  controlled_preserves _ _ (original_load_preserves time)
    (preserves_smul (original_load_preserves time) (freePhase time : ℂ))

theorem weak_pointer_preserves (time : ℝ) :
    Preserves pointerOrbit (Weak.pointerPulse time : PointerJoint) :=
  controlled_preserves _ _ (original_load_preserves time)
    (preserves_smul (weak_pulse_preserves time) (freePhase time : ℂ))

open Propagation.Producer in
def nineWord : Matrix.unitaryGroup PointerIndex ℂ :=
  Pointer.loadPulse (nativeClockStep : ℝ) * feedbackPulse (nativeClockStep : ℝ) *
    feedbackPulse (nativeClockStep : ℝ) * sourceUnitary

theorem nineWord_actual : Weak.origin.action = nineWord := by
  change (Pointer.loadPulse _ * (feedbackPulse _ * (feedbackPulse _ * (sourceUnitary * 1)))) = _
  simp only [nineWord, mul_one, mul_assoc]

theorem nineWord_preserves : Preserves pointerOrbit (nineWord : PointerJoint) := by
  unfold nineWord
  simp only [MulMemClass.coe_mul]
  exact preserves_mul (preserves_mul (preserves_mul (pointer_load_preserves _)
    (feedback_preserves _)) (feedback_preserves _)) original_dilation_preserves

open Propagation.Producer in
def elevenWord : Matrix.unitaryGroup PointerIndex ℂ :=
  Pointer.loadPulse (nativeClockStep : ℝ) * Weak.pointerPulse (nativeClockStep : ℝ) * nineWord

theorem elevenWord_actual : Weak.execution.action = elevenWord := by
  change (Pointer.loadPulse _ * (Weak.pointerPulse _ * Weak.origin.action)) = _
  rw [nineWord_actual]
  simp only [elevenWord, mul_assoc]

theorem elevenWord_preserves : Preserves pointerOrbit (elevenWord : PointerJoint) := by
  unfold elevenWord
  simp only [MulMemClass.coe_mul]
  exact preserves_mul (preserves_mul (pointer_load_preserves _) (weak_pointer_preserves _)) nineWord_preserves

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
