import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Gain

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A shared earlier history cancels isometrically in the actual net observable. -/
theorem shared_suffix_difference (A B : Matrix.unitaryGroup ι ℂ) (O : Matrix ι ι ℂ) :
    ‖Quantum.conjugation (star (A*B)) O-Quantum.conjugation (star B) O‖ =
      ‖Quantum.conjugation (star A) O-O‖ := by
  rw [star_mul,← Environment.conjugation_comp,← map_sub]
  exact StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (star B)) _

theorem two_pulse_difference (A B : Matrix.unitaryGroup ι ℂ) (O : Matrix ι ι ℂ) :
    ‖Quantum.conjugation (star (A*B)) O-O‖ ≤
      ‖Quantum.conjugation (star A) O-O‖+‖Quantum.conjugation (star B) O-O‖ := by
  rw [star_mul,← Environment.conjugation_comp]
  have split : Quantum.conjugation (star B) (Quantum.conjugation (star A) O)-O=
      Quantum.conjugation (star B) (Quantum.conjugation (star A) O-O)+(Quantum.conjugation (star B) O-O) := by
    rw [map_sub]
    abel
  rw [split]
  apply (norm_add_le _ _).trans
  exact add_le_add (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (star B)) _).le le_rfl

theorem original_gain_suffix_norm (O : PointerJoint) :
    ‖gainObservable O‖=‖Quantum.conjugation
      (star (loadPulse (nativeClockStep : ℝ)*Weak.pointerPulse (nativeClockStep : ℝ))) O-O‖ := by
  unfold gainObservable afterInstrumentEleven
  exact shared_suffix_difference _ _ O

theorem original_gain_two_pulse_bound (O : PointerJoint) :
    ‖gainObservable O‖ ≤
      ‖Quantum.conjugation (star (loadPulse (nativeClockStep : ℝ))) O-O‖+
      ‖Quantum.conjugation (star (Weak.pointerPulse (nativeClockStep : ℝ))) O-O‖ := by
  rw [original_gain_suffix_norm]
  exact two_pulse_difference _ _ O

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
