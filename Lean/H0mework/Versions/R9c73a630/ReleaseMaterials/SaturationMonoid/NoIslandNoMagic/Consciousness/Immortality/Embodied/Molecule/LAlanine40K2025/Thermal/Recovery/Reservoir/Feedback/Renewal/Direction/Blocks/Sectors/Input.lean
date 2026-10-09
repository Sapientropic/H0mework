import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Sectors.Dynamics

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix ComplexOrder
noncomputable section

/-- The original received 4q body, donor and environment are retained before the first supply. -/
def inputFour : PointerJoint := prepared (Incidence.receivedJoint Source.received.joint Source.donor)

def firstSupply : Matrix.unitaryGroup PointerIndex ℂ :=
  blockUnitary (Current.pulse (nativeClockStep : ℝ)) (Current.pulse (nativeClockStep : ℝ))

theorem source_initial_from_four : sourceInitial = Quantum.conjugation firstSupply inputFour := by
  unfold sourceInitial Pointer.received
  rw [Current.supplyNext_joint,Current.initial_receives_actual,Pointer.Environment.prepared_conjugation]
  rfl

def nineAction : Matrix.unitaryGroup PointerIndex ℂ := nineWord * firstSupply
def elevenAction : Matrix.unitaryGroup PointerIndex ℂ := elevenWord * firstSupply

theorem actual_nine_from_four : Weak.origin.joint = Quantum.conjugation nineAction inputFour := by
  change Quantum.conjugation Weak.origin.action sourceInitial = _
  rw [nineWord_actual,source_initial_from_four,Environment.conjugation_comp]
  rfl

theorem actual_eleven_from_four : Weak.execution.joint = Quantum.conjugation elevenAction inputFour := by
  change Quantum.conjugation Weak.execution.action sourceInitial = _
  rw [elevenWord_actual,source_initial_from_four,Environment.conjugation_comp]
  rfl

theorem first_supply_preserves : Preserves pointerOrbit (firstSupply : PointerJoint) :=
  controlled_preserves _ _ (original_pulse_preserves _) (original_pulse_preserves _)

theorem nine_action_preserves : Preserves pointerOrbit (nineAction : PointerJoint) :=
  preserves_mul nineWord_preserves first_supply_preserves

theorem eleven_action_preserves : Preserves pointerOrbit (elevenAction : PointerJoint) :=
  preserves_mul elevenWord_preserves first_supply_preserves

theorem actual_nine_sector (k : Sym2 (Sym2 Basis)) :
    restrict pointerOrbit k Weak.origin.joint =
      restrict pointerOrbit k (nineAction : PointerJoint) * restrict pointerOrbit k inputFour *
        (restrict pointerOrbit k (nineAction : PointerJoint))ᴴ := by
  rw [actual_nine_from_four]
  exact restrict_conjugation nineAction nine_action_preserves inputFour k

theorem actual_eleven_sector (k : Sym2 (Sym2 Basis)) :
    restrict pointerOrbit k Weak.execution.joint =
      restrict pointerOrbit k (elevenAction : PointerJoint) * restrict pointerOrbit k inputFour *
        (restrict pointerOrbit k (elevenAction : PointerJoint))ᴴ := by
  rw [actual_eleven_from_four]
  exact restrict_conjugation elevenAction eleven_action_preserves inputFour k

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
