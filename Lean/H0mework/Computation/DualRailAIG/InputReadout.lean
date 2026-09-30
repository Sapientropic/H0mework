import H0mework.Computation.DualRailAIG.InputWindow
import H0mework.Computation.DualRailAIG.InputClock

/-! # Source-clocked readout inside the actual input-voltage lease -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface Set
open Netlist.Dissipative.Dimensioned.Driven.Producer

noncomputable section

variable {α : Type} [DecidableEq α] [Hashable α]

def aigInputSampledTime (technology : AIGCellTechnology) (graph : AIG α) (first : ℝ)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) : SISecond :=
  finiteSamplingClockSampleTime clock code ⟨first + (aigDualRailGraphDeadline technology graph).value⟩

theorem aigInputSampledTime_late (technology : AIGCellTechnology) (graph : AIG α) (first : ℝ)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    first + (aigDualRailGraphDeadline technology graph).value ≤
      (aigInputSampledTime technology graph first clock code).value :=
  finiteSamplingClock_requested_le_sampleTime clock code _

theorem aigInputSampledTime_lt_deadline_add_tick
    (technology : AIGCellTechnology) (graph : AIG α) (first : ℝ) (firstNonnegative : 0 ≤ first)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    (aigInputSampledTime technology graph first clock code).value <
      first + (aigDualRailGraphDeadline technology graph).value +
        (finiteSamplingClockTickPeriod clock code).value :=
  finiteSamplingClock_sampleTime_lt_requested_add_tick clock code _
    (add_nonneg firstNonnegative (aigDualRailGraphDeadline_nonneg technology graph))

def aigInputSampledRead (technology : AIGCellTechnology) (graph : AIG α)
    (input : α → ℝ → SIVolt) (initial : Fin graph.decls.size → Bool → SIVolt) (first : ℝ)
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) (ref : AIG.Ref graph) : Option Bool :=
  railRead? (compileDualRailCell technology graph ⟨ref.gate, ref.hgate⟩ ref.invert)
    ((compileAIGDualRailTrajectoryFromInputs technology graph input initial ⟨ref.gate, ref.hgate⟩).wave
      ref.invert (aigInputSampledTime technology graph first clock code).value)

theorem aigInputSampledRead_eq_denote_of_window
    (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology graph node polarity) (initial node polarity))
    (inputContinuous : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))
    (assign : α → Bool) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (inputBands : ∀ (node : Fin graph.decls.size) atom,
      graph.decls[node.val] = .atom atom → ∀ t ∈ Icc first last,
        BitBand (compileDualRailCell technology graph node false) (assign atom) (input atom t))
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (leaseCoversSample : (aigInputSampledTime technology graph first clock code).value ≤ last)
    (ref : AIG.Ref graph) :
    aigInputSampledRead technology graph input initial first clock code ref =
      some (AIG.denote assign ⟨graph, ref⟩) := by
  have actual := compileAIGDualRailTrajectoryFromInputs_window technology graph input initial initialRail
    inputContinuous assign first last firstNonnegative inputBands ⟨ref.gate, ref.hgate⟩ ref.invert
  have delay := compileAIGDualRailTrajectoryFromInputs_ready_le_graphDeadline technology graph input initial
    ⟨ref.gate, ref.hgate⟩ ref.invert
  have late : first + (compileAIGDualRailTrajectoryFromInputs technology graph input initial
      ⟨ref.gate, ref.hgate⟩).ready ref.invert ≤ (aigInputSampledTime technology graph first clock code).value := by
    linarith [aigInputSampledTime_late technology graph first clock code]
  have band := actual.settled _ ⟨late, leaseCoversSample⟩
  change BitBand _ (AIG.denote assign ⟨graph, ref⟩) _ at band
  cases result : AIG.denote assign ⟨graph, ref⟩
  · exact railRead?_of_low _ _ (by simpa only [result, BitBand, Bool.false_eq_true, ↓reduceIte] using band)
  · exact railRead?_of_high _ _ (by simpa only [result, BitBand, ↓reduceIte] using band)

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
