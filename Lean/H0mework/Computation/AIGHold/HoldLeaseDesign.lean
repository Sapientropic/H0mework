import H0mework.Computation.AIGHold.ClockedLeakyHold
import H0mework.Computation.DualRailAIG.InputReadout

/-!
# The actual downstream graph and source clock size the finite hold lease

The resistance is a generated value in the explicit switching-RC model. The
same capacitor, downstream signed loads and clock period determine it; neither
an assignment, a capture certificate nor a requested logical result is input.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Cells.Conductance Set
open Netlist.Dissipative.Dimensioned.Driven.Producer

noncomputable section

variable {α : Type} [DecidableEq α] [Hashable α]

def compileHoldLeaseForGraph (source : LoadedConductanceCellSource)
    (downstreamTechnology : AIGCellTechnology) (graph : AIG α)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    ClockedLeakyHoldSource source where
  holdResistance := ⟨16 * ((aigDualRailGraphDeadline downstreamTechnology graph).value +
    (finiteSamplingClockTickPeriod clock code).value) / source.capacitance.value⟩
  holdResistance_pos := div_pos
    (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos
      (aigDualRailGraphDeadline_nonneg downstreamTechnology graph)
      (finiteSamplingClockTickPeriod_pos clock code))) source.capacitance_pos

theorem compileHoldLeaseForGraph_retentionTime (source : LoadedConductanceCellSource)
    (downstreamTechnology : AIGCellTechnology) (graph : AIG α)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    (compileHoldLeaseForGraph source downstreamTechnology graph clock code).retentionTime.value =
      (aigDualRailGraphDeadline downstreamTechnology graph).value +
        (finiteSamplingClockTickPeriod clock code).value := by
  have capNonzero := ne_of_gt source.capacitance_pos
  dsimp only [compileHoldLeaseForGraph, ClockedLeakyHoldSource.retentionTime,
    ClockedLeakyHoldSource.timeConstant]
  field_simp

theorem compileHoldLeaseForGraph_sample_lt_lease_end (source : LoadedConductanceCellSource)
    (downstreamTechnology : AIGCellTechnology) (graph : AIG α)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (stopTime : ℝ) (stopNonnegative : 0 ≤ stopTime) :
    (aigInputSampledTime downstreamTechnology graph stopTime clock code).value <
      stopTime + (compileHoldLeaseForGraph source downstreamTechnology graph clock code).retentionTime.value := by
  rw [compileHoldLeaseForGraph_retentionTime, ← add_assoc]
  exact aigInputSampledTime_lt_deadline_add_tick downstreamTechnology graph stopTime stopNonnegative clock code

theorem compileHoldLeaseForGraph_sample_mem_lease (source : LoadedConductanceCellSource)
    (downstreamTechnology : AIGCellTechnology) (graph : AIG α)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (stopTime : ℝ) (stopNonnegative : 0 ≤ stopTime) :
    (aigInputSampledTime downstreamTechnology graph stopTime clock code).value ∈
      Icc stopTime
        (stopTime + (compileHoldLeaseForGraph source downstreamTechnology graph clock code).retentionTime.value) := by
  constructor
  · exact (le_add_of_nonneg_right (aigDualRailGraphDeadline_nonneg downstreamTechnology graph)).trans
      (aigInputSampledTime_late downstreamTechnology graph stopTime clock code)
  · exact (compileHoldLeaseForGraph_sample_lt_lease_end source downstreamTechnology graph clock code
      stopTime stopNonnegative).le

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
