import H0mework.Computation.ADCMicro.RawPhaseCalls

/-!
# Once-installed raw receiver graphs

The program stores the two width-dependent compiler images before any packet is
received. Its proof-only lineage fixes both graph declarations and terminal
references. Calls start empty owned tables against these stored graphs; completed
outputs only read those tables. Packet data and expected answers are not compiler
inputs. The five fixed 128-bit graphs remain the existing closed constants.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat
open Std.Tactic.BVDecide

/-- Stored source compiler images, with no packet, acceptance bit, or future table. -/
structure FiniteADCRawInstalledProgram (code : FiniteADCResolutionCode) (counterBits : Nat) where
  packetGraph : AIG.Entrypoint BVBit
  calibrationGraph : AIG.Entrypoint BVBit
  packet_source : packetGraph = finiteADCRawPacketGraph code counterBits
  calibration_source : calibrationGraph = finiteADCRawCalibrationGraph code

/-- Compile the source configuration once, independently of every later packet. -/
def compileFiniteADCRawInstalledProgram (code : FiniteADCResolutionCode) (counterBits : Nat) :
    FiniteADCRawInstalledProgram code counterBits where
  packetGraph := finiteADCRawPacketGraph code counterBits
  calibrationGraph := finiteADCRawCalibrationGraph code
  packet_source := rfl
  calibration_source := rfl

namespace FiniteADCRawInstalledProgram

variable {code : FiniteADCResolutionCode} {counterBits : Nat}

private theorem source_ref_cast_eq (left right : AIG.Entrypoint BVBit) (same : left = right) :
    left.ref.cast (Nat.le_of_eq (congrArg (fun graph => graph.aig.decls.size) same)) =
      right.ref := by
  cases same
  rfl

/-- Source lineage determines all stored program data, including terminal references. -/
theorem eq_compile (program : FiniteADCRawInstalledProgram code counterBits) :
    program = compileFiniteADCRawInstalledProgram code counterBits := by
  rcases program with ⟨packet, calibration, packetSource, calibrationSource⟩
  subst packet
  subst calibration
  rfl

theorem unique (left right : FiniteADCRawInstalledProgram code counterBits) :
    left = right :=
  left.eq_compile.trans right.eq_compile.symm

theorem packet_size_eq (program : FiniteADCRawInstalledProgram code counterBits) :
    program.packetGraph.aig.decls.size =
      (finiteADCRawPacketGraph code counterBits).aig.decls.size := by
  rw [program.packet_source]

theorem calibration_size_eq (program : FiniteADCRawInstalledProgram code counterBits) :
    program.calibrationGraph.aig.decls.size =
      (finiteADCRawCalibrationGraph code).aig.decls.size := by
  rw [program.calibration_source]

theorem packet_ref_eq (program : FiniteADCRawInstalledProgram code counterBits) :
    program.packetGraph.ref.cast (Nat.le_of_eq program.packet_size_eq) =
      (finiteADCRawPacketGraph code counterBits).ref := by
  exact source_ref_cast_eq _ _ program.packet_source

theorem calibration_ref_eq (program : FiniteADCRawInstalledProgram code counterBits) :
    program.calibrationGraph.ref.cast (Nat.le_of_eq program.calibration_size_eq) =
      (finiteADCRawCalibrationGraph code).ref := by
  exact source_ref_cast_eq _ _ program.calibration_source

end FiniteADCRawInstalledProgram

/-- Empty source-owned work table over the already installed packet graph. -/
def finiteADCRawProgramPacketCall
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits) :
    AIGOwnedProgress program.packetGraph.aig
      (finiteADCRawPacketPhaseAssignment code lastTick packet) :=
  aigOwnedProgressBoot _ _

/-- The packet result reads the stored terminal reference in its current completed table. -/
def finiteADCRawProgramPacketOutput
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits)
    (current : AIGOwnedProgress program.packetGraph.aig
      (finiteADCRawPacketPhaseAssignment code lastTick packet))
    (complete : program.packetGraph.aig.decls.size ≤ current.ticks) : Bool :=
  aigOwnedProgressReadAt current ((aigOwnedProgress_complete_iff current).mpr complete)
    program.packetGraph.ref

/-- Calibration starts only from the packet receipt, on the installed calibration graph. -/
def finiteADCRawProgramCalibrationCall
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) :
    AIGOwnedProgress program.calibrationGraph.aig
      (finiteADCRawCalibrationPhaseAssignment checked) :=
  aigOwnedProgressBoot _ _

def finiteADCRawProgramCalibrationOutput
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
    (current : AIGOwnedProgress program.calibrationGraph.aig
      (finiteADCRawCalibrationPhaseAssignment checked))
    (complete : program.calibrationGraph.aig.decls.size ≤ current.ticks) : Bool :=
  aigOwnedProgressReadAt current ((aigOwnedProgress_complete_iff current).mpr complete)
    program.calibrationGraph.ref

/-- Owned execution determines the packet verdict; source identity then identifies its specification. -/
theorem finiteADCRawProgramPacketOutput_eq
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits)
    (current : AIGOwnedProgress program.packetGraph.aig
      (finiteADCRawPacketPhaseAssignment code lastTick packet))
    (complete : program.packetGraph.aig.decls.size ≤ current.ticks) :
    finiteADCRawProgramPacketOutput program lastTick packet current complete =
      finiteADCRawPacketGateRunFor code lastTick packet := by
  unfold finiteADCRawProgramPacketOutput
  rw [aigOwnedProgressReadAt_eq_read]
  rw [program.packet_source]
  rfl

theorem finiteADCRawProgramCalibrationOutput_eq
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits)
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick)
    (current : AIGOwnedProgress program.calibrationGraph.aig
      (finiteADCRawCalibrationPhaseAssignment checked))
    (complete : program.calibrationGraph.aig.decls.size ≤ current.ticks) :
    finiteADCRawProgramCalibrationOutput program checked current complete =
      finiteADCRawCalibrationGateRunFor code lastTick checked.packet := by
  unfold finiteADCRawProgramCalibrationOutput
  rw [aigOwnedProgressReadAt_eq_read]
  rw [program.calibration_source]
  rfl

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
