import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.PointerConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Sectors.Input

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Propagation.Producer Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def afterInstrumentNine : Matrix.unitaryGroup PointerIndex ℂ :=
  loadPulse (nativeClockStep : ℝ)*feedbackPulse (nativeClockStep : ℝ)*feedbackPulse (nativeClockStep : ℝ)
def afterInstrumentEleven : Matrix.unitaryGroup PointerIndex ℂ :=
  loadPulse (nativeClockStep : ℝ)*Weak.pointerPulse (nativeClockStep : ℝ)*afterInstrumentNine

attribute [local irreducible] sourceInitial sourceTarget sourceUnitary Weak.origin Weak.execution
  approximatedPointerUnitary afterInstrumentNine afterInstrumentEleven

theorem original_nine_from_instrument : Weak.origin.joint = Quantum.conjugation afterInstrumentNine sourceTarget := by
  change Quantum.conjugation Weak.origin.action sourceInitial = _
  rw [Sectors.nineWord_actual,sourceTarget_generated]
  rw [Environment.conjugation_comp]
  have words : Sectors.nineWord = afterInstrumentNine*sourceUnitary := by
    unfold Sectors.nineWord afterInstrumentNine
    rfl
  exact congrArg (fun U : Matrix.unitaryGroup PointerIndex ℂ => Quantum.conjugation U sourceInitial) words

theorem original_eleven_from_instrument : Weak.execution.joint = Quantum.conjugation afterInstrumentEleven sourceTarget := by
  change Quantum.conjugation Weak.execution.action sourceInitial = _
  rw [Sectors.elevenWord_actual,sourceTarget_generated,Environment.conjugation_comp]
  have words : Sectors.elevenWord = afterInstrumentEleven*sourceUnitary := by
    simp only [Sectors.elevenWord,Sectors.nineWord,afterInstrumentEleven,afterInstrumentNine,mul_assoc]
  exact congrArg (fun U : Matrix.unitaryGroup PointerIndex ℂ => Quantum.conjugation U sourceInitial) words

def approximatedNine (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) : PointerJoint :=
  Quantum.conjugation afterInstrumentNine
    (Quantum.conjugation (approximatedPointerUnitary B hermitian) sourceInitial)
def approximatedEleven (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) : PointerJoint :=
  Quantum.conjugation afterInstrumentEleven
    (Quantum.conjugation (approximatedPointerUnitary B hermitian) sourceInitial)

private theorem common_conjugation_error (U : Matrix.unitaryGroup PointerIndex ℂ) (rho sigma : PointerJoint) :
    ‖Quantum.conjugation U rho-Quantum.conjugation U sigma‖ = ‖rho-sigma‖ := by
  rw [← map_sub]
  exact StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (PointerJoint) U) _

theorem original_nine_instrument_error (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) :
    ‖Weak.origin.joint-approximatedNine B hermitian‖ ≤
      4*rootErrorBudget (sourceOutputObservable Load.Source.loadTotalHamiltonian) B*‖sourceInitial‖ := by
  rw [original_nine_from_instrument,approximatedNine,common_conjugation_error]
  exact original_pointer_state_error B hermitian

theorem original_eleven_instrument_error (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) :
    ‖Weak.execution.joint-approximatedEleven B hermitian‖ ≤
      4*rootErrorBudget (sourceOutputObservable Load.Source.loadTotalHamiltonian) B*‖sourceInitial‖ := by
  rw [original_eleven_from_instrument,approximatedEleven,common_conjugation_error]
  exact original_pointer_state_error B hermitian

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
