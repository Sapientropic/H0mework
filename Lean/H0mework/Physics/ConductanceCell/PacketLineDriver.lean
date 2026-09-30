import H0mework.Physics.ConductanceCell.PacketLineLoad

/-!
# Source-bit controlled, actually evolving packet input lines

Each original packet bit clamps the two controls of a loaded NAND to its
complementary supply rail. The output capacitor evolves from its actual
initial voltage. This is the existing quartic conductance/clamped-supply model;
no output band, ODE solution or receiver verdict is supplied to the producer.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface Set

variable {α : Type} [DecidableEq α] [Hashable α]

noncomputable section

def packetLineControl (source : LoadedConductanceCellSource) (bit : Bool) : SIVolt :=
  if bit then ⟨0⟩ else source.supply

theorem packetLineControl_band (source : LoadedConductanceCellSource) (bit : Bool) :
    BitBand source (!bit) (packetLineControl source bit) := by
  cases bit <;> simp only [packetLineControl, BitBand, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, HighBand, LowBand]
  · exact ⟨by linarith [source.supply_pos], le_rfl⟩
  · exact ⟨le_rfl, by linarith [source.supply_pos]⟩

def packetLineInputWave (technology : AIGCellTechnology) (graph : AIG α) (assignment : α → Bool)
    (initial : α → SIVolt) (atom : α) (time : ℝ) : SIVolt :=
  let driver := compilePacketLineDriver technology graph atom
  let control := packetLineControl driver (assignment atom)
  driver.flowAt control control (initial atom) ⟨time⟩

theorem packetLineInputWave_initial (technology : AIGCellTechnology) (graph : AIG α)
    (assignment : α → Bool) (initial : α → SIVolt) (atom : α) :
    packetLineInputWave technology graph assignment initial atom 0 = initial atom :=
  (compilePacketLineDriver technology graph atom).flowAt_initial _ _ _

theorem packetLineInputWave_kcl (technology : AIGCellTechnology) (graph : AIG α)
    (assignment : α → Bool) (initial : α → SIVolt) (atom : α) (time : ℝ) :
    let driver := compilePacketLineDriver technology graph atom
    let control := packetLineControl driver (assignment atom)
    HasDerivAt (fun t => (packetLineInputWave technology graph assignment initial atom t).value)
      ((driver.pullUp control control *
          (driver.supply.value - (packetLineInputWave technology graph assignment initial atom time).value) -
        driver.pullDown control control *
          (packetLineInputWave technology graph assignment initial atom time).value) /
            driver.capacitance.value) time :=
  (compilePacketLineDriver technology graph atom).voltageAt_kcl _ _ _ _

theorem packetLineInputWave_continuous (technology : AIGCellTechnology) (graph : AIG α)
    (assignment : α → Bool) (initial : α → SIVolt) (atom : α) :
    Continuous (fun t => (packetLineInputWave technology graph assignment initial atom t).value) :=
  continuous_iff_continuousAt.mpr (fun time =>
    (packetLineInputWave_kcl technology graph assignment initial atom time).continuousAt)

theorem packetLineInputWave_mem_rail (technology : AIGCellTechnology) (graph : AIG α)
    (assignment : α → Bool) (initial : α → SIVolt) (atom : α)
    (initialRail : InRail (compilePacketLineDriver technology graph atom) (initial atom))
    (time : ℝ) (nonnegative : 0 ≤ time) :
    InRail (compilePacketLineDriver technology graph atom)
      (packetLineInputWave technology graph assignment initial atom time) :=
  (compilePacketLineDriver technology graph atom).voltageAt_mem_rail _ _ _ initialRail time nonnegative

theorem packetLineInputWave_settled (technology : AIGCellTechnology) (graph : AIG α)
    (assignment : α → Bool) (initial : α → SIVolt) (atom : α)
    (initialRail : InRail (compilePacketLineDriver technology graph atom) (initial atom))
    (time : ℝ) (late : (compilePacketLineDriver technology graph atom).settlingTime.value ≤ time) :
    BitBand (compilePacketLineDriver technology graph atom) (assignment atom)
      (packetLineInputWave technology graph assignment initial atom time) := by
  let driver := compilePacketLineDriver technology graph atom
  let control := packetLineControl driver (assignment atom)
  have band := driver.flowAt_nand_band (!(assignment atom)) (!(assignment atom))
    control control (initial atom) (packetLineControl_band driver (assignment atom))
    (packetLineControl_band driver (assignment atom)) initialRail ⟨time⟩ late
  simpa only [Bool.and_self, Bool.not_not, packetLineInputWave, driver, control] using band

theorem packetLineInputWave_registered_band (technology : AIGCellTechnology) (graph : AIG α)
    (assignment : α → Bool) (initial : α → SIVolt) (atom : α)
    (node : Fin graph.decls.size) (registered : graph.decls[node.val] = .atom atom)
    (initialRail : InRail (compilePacketLineDriver technology graph atom) (initial atom))
    (time : ℝ) (late : (packetLineReadyTime technology graph).value ≤ time) :
    BitBand (compileDualRailCell technology graph node false) (assignment atom)
      (packetLineInputWave technology graph assignment initial atom time) := by
  change BitBand (compilePacketLineDriver technology graph atom) (assignment atom) _
  exact packetLineInputWave_settled technology graph assignment initial atom initialRail time
    ((packetLineDriver_wait_le_ready technology graph atom node registered).trans late)

/-- These are the two independent input consumers of the existing whole-graph window theorem. -/
theorem packetLineInputWave_registered_consumers (technology : AIGCellTechnology) (graph : AIG α)
    (assignment : α → Bool) (initial : α → SIVolt)
    (initialRail : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom →
        InRail (compilePacketLineDriver technology graph atom) (initial atom))
    (last : ℝ) :
    (∀ (node : Fin graph.decls.size) atom, graph.decls[node.val] = .atom atom →
      Continuous (fun t => (packetLineInputWave technology graph assignment initial atom t).value)) ∧
    (∀ (node : Fin graph.decls.size) atom, graph.decls[node.val] = .atom atom →
      ∀ t ∈ Icc (packetLineReadyTime technology graph).value last,
        BitBand (compileDualRailCell technology graph node false) (assignment atom)
          (packetLineInputWave technology graph assignment initial atom t)) := by
  constructor
  · intro _ atom _
    exact packetLineInputWave_continuous technology graph assignment initial atom
  · intro node atom registered time window
    exact packetLineInputWave_registered_band technology graph assignment initial atom node registered
      (initialRail node atom registered) time window.1

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
