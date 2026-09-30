import H0mework.Computation.AIGHold.AIGMemoryEndpoint
import H0mework.Computation.AIGHold.AIGHeldStateReadout

/-! # A new input command restarts from actual memory endpoints without resetting charge -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

theorem aigOutputBank_noncapacitive_is_old (entry : AIG.RefVecEntry α width)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool)
    (notCapacitive : ¬aigNodeHasCapacitor (aigOutputBank entry).aig node polarity = true) :
    node.val < entry.aig.decls.size := by
  by_contra notOld
  have bound : node.val - entry.aig.decls.size < width := by
    have size := aigOutputBank_size entry
    have indexBound := node.isLt
    omega
  have added := aigOutputBankDecls_new entry ⟨node.val - entry.aig.decls.size, bound⟩
  have address : entry.aig.decls.size + (node.val - entry.aig.decls.size) = node.val := by omega
  simp only [address] at added
  have selected : (aigOutputBank entry).aig.decls[node.val] =
      .gate (.mk (entry.vec.get (node.val - entry.aig.decls.size) bound).gate
        (entry.vec.get (node.val - entry.aig.decls.size) bound).invert) (.mk 0 true) := added
  exact notCapacitive (by simp only [aigNodeHasCapacitor, selected])

noncomputable section

theorem aigMemoryStateAt_initial (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) :
    aigMemoryStateAt technology entry memory assignment downstreamTechnology downstreamGraph clock code node polarity 0 =
      memory.gateInitial node polarity := by
  rw [aigMemoryStateAt, aigHeldBankStateAt_initial]
  cases selected : (aigOutputBank entry).aig.decls[node.val] with
  | false =>
    cases polarity <;> simp only [selected, AIGCapacitorMemory.gateInitial,
      aigNodeHasCapacitor, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
  | atom atom =>
    cases polarity
    · simp only [selected, aigMemoryInputWave, packetLineInputWave_initial,
        AIGCapacitorMemory.gateInitial, aigNodeHasCapacitor, Bool.false_eq_true, ↓reduceDIte]
    · rfl
  | gate left right =>
    rfl

theorem aigMemoryStateAt_restart (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig)
    (oldAssignment newAssignment : α → Bool)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (time : ℝ) (nonnegative : 0 ≤ time)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) :
    aigMemoryStateAt technology entry
        (aigMemoryEndpoint technology entry memory oldAssignment downstreamTechnology downstreamGraph clock code time nonnegative)
        newAssignment downstreamTechnology downstreamGraph clock code node polarity 0 =
      aigMemoryStateAt technology entry memory oldAssignment downstreamTechnology downstreamGraph clock code node polarity time := by
  rw [aigMemoryStateAt_initial]
  by_cases capacitive : aigNodeHasCapacitor (aigOutputBank entry).aig node polarity = true
  · exact aigMemoryEndpoint_cell_exact technology entry memory oldAssignment downstreamTechnology downstreamGraph
      clock code time nonnegative (⟨(node, polarity), capacitive⟩ : AIGCapacitorAddress (aigOutputBank entry).aig)
  · have old := aigOutputBank_noncapacitive_is_old entry node polarity capacitive
    rw [AIGCapacitorMemory.gateInitial, dif_neg capacitive]
    rw [aigMemoryStateAt, aigHeldBankStateAt_old technology entry _ _ _ _ _ _ _ node old]
    have equation := compileAIGDualRailTrajectoryFromInputs.eq_def technology (aigOutputBank entry).aig
      (aigMemoryInputWave technology entry memory oldAssignment) memory.gateInitial node
    split at equation
    · rename_i selected
      rw [equation]
      cases polarity <;> simp only [selected, AIGDualRailTrajectory.wave_false,
        AIGDualRailTrajectory.wave_true, Bool.false_eq_true, ↓reduceIte]
    · rename_i atom selected
      rw [equation]
      cases polarity
      · simp only [selected, AIGDualRailTrajectory.wave_false]
        exact aigMemoryEndpoint_input_exact technology entry memory oldAssignment downstreamTechnology downstreamGraph
          clock code time nonnegative (⟨atom, ⟨node, selected⟩⟩ : AIGInputPort (aigOutputBank entry).aig)
      · exact False.elim (capacitive (by simp only [aigNodeHasCapacitor, selected]))
    · rename_i left right selected
      exact False.elim (capacitive (by simp only [aigNodeHasCapacitor, selected]))

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
