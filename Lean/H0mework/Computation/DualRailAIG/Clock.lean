import H0mework.Computation.DualRailAIG.Trajectory

/-!
# Input-independent clock of the literal dual-rail source graph

Only declaration addresses and their signed capacitive loads generate ready
times. The separate recursion exposes this independence without supplying a
dummy assignment, an initial state, or any requested logical output.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface
open Netlist.Dissipative.Dimensioned.Driven.Producer

noncomputable section

def aigDualRailReadyAt {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α)
    (node : Fin graph.decls.size) (polarity : Bool) : ℝ :=
  match declaration : graph.decls[node.val] with
  | .false => 0
  | .atom _ =>
      if polarity then (compileDualRailCell technology graph node true).settlingTime.value else 0
  | .gate left right =>
      have fanins := graph.hdag node.isLt declaration
      let leftReady := aigDualRailReadyAt technology graph ⟨left.gate, by omega⟩ left.invert
      let rightReady := aigDualRailReadyAt technology graph ⟨right.gate, by omega⟩ right.invert
      let negativeReady := max leftReady rightReady +
        (compileDualRailCell technology graph node true).settlingTime.value
      if polarity then negativeReady else
        negativeReady + (compileDualRailCell technology graph node false).settlingTime.value
termination_by (node.val, 0)

theorem compileAIGDualRailTrajectory_ready_eq_source
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (assign : α → Bool)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    (compileAIGDualRailTrajectory technology graph assign initial node).ready polarity =
      aigDualRailReadyAt technology graph node polarity := by
  rw [compileAIGDualRailTrajectory.constructor_eq]
  split
  · rw [aigDualRailReadyAt.eq_def]
    dsimp only [AIGDualRailTrajectory.ready]
    cases polarity <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> simp_all
  · rw [aigDualRailReadyAt.eq_def]
    dsimp only [AIGDualRailTrajectory.ready]
    cases polarity <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> simp_all
  · rename_i left right declaration
    have fanins := graph.hdag node.isLt declaration
    have leftRead := compileAIGDualRailTrajectory_ready_eq_source technology graph assign initial
      ⟨left.gate, by omega⟩ left.invert
    have rightRead := compileAIGDualRailTrajectory_ready_eq_source technology graph assign initial
      ⟨right.gate, by omega⟩ right.invert
    rw [aigDualRailReadyAt.eq_def]
    split <;> simp_all [AIGDualRailTrajectory.ready]
    rename_i left' right' sameDeclaration
    obtain ⟨rfl, rfl⟩ := AIG.Decl.gate.inj (declaration.symm.trans sameDeclaration)
    rfl
termination_by (node.val, 0)

theorem aigDualRailReadyAt_nonneg {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α)
    (node : Fin graph.decls.size) (polarity : Bool) :
    0 ≤ aigDualRailReadyAt technology graph node polarity := by
  rw [aigDualRailReadyAt.eq_def]
  split
  · exact le_rfl
  · cases polarity
    · exact le_rfl
    · exact (compileDualRailCell technology graph node true).settlingTime_pos.le
  · rename_i left right declaration
    have fanins := graph.hdag node.isLt declaration
    have leftNonnegative := aigDualRailReadyAt_nonneg technology graph
      ⟨left.gate, by omega⟩ left.invert
    have firstNonnegative : 0 ≤ max
        (aigDualRailReadyAt technology graph ⟨left.gate, by omega⟩ left.invert)
        (aigDualRailReadyAt technology graph ⟨right.gate, by omega⟩ right.invert) :=
      le_trans leftNonnegative (le_max_left _ _)
    have negativeNonnegative := add_nonneg firstNonnegative
      (compileDualRailCell technology graph node true).settlingTime_pos.le
    cases polarity
    · exact add_nonneg negativeNonnegative
        (compileDualRailCell technology graph node false).settlingTime_pos.le
    · exact negativeNonnegative
termination_by (node.val, 0)

theorem compileAIGDualRailTrajectory_ready_nonneg
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (assign : α → Bool)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    0 ≤ (compileAIGDualRailTrajectory technology graph assign initial node).ready polarity := by
  rw [compileAIGDualRailTrajectory_ready_eq_source]
  exact aigDualRailReadyAt_nonneg technology graph node polarity

theorem compileAIGDualRailTrajectory_ready_independent
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (assign₁ assign₂ : α → Bool)
    (initial₁ initial₂ : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    (compileAIGDualRailTrajectory technology graph assign₁ initial₁ node).ready polarity =
      (compileAIGDualRailTrajectory technology graph assign₂ initial₂ node).ready polarity := by
  rw [compileAIGDualRailTrajectory_ready_eq_source, compileAIGDualRailTrajectory_ready_eq_source]

def aigDualRailGraphDeadline {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) : SISecond :=
  ⟨(Finset.univ : Finset (Fin graph.decls.size × Bool)).sup'
    ⟨(⟨0, graph.hzero⟩, false), Finset.mem_univ _⟩
    (fun address => aigDualRailReadyAt technology graph address.1 address.2)⟩

theorem aigDualRailReadyAt_le_graphDeadline {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α)
    (node : Fin graph.decls.size) (polarity : Bool) :
    aigDualRailReadyAt technology graph node polarity ≤ (aigDualRailGraphDeadline technology graph).value :=
  Finset.le_sup' (fun address : Fin graph.decls.size × Bool =>
    aigDualRailReadyAt technology graph address.1 address.2) (Finset.mem_univ (node, polarity))

theorem aigDualRailGraphDeadline_nonneg {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) :
    0 ≤ (aigDualRailGraphDeadline technology graph).value :=
  (aigDualRailReadyAt_nonneg technology graph ⟨0, graph.hzero⟩ false).trans
    (aigDualRailReadyAt_le_graphDeadline technology graph ⟨0, graph.hzero⟩ false)

theorem compileAIGDualRailTrajectory_ready_le_graphDeadline
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (assign : α → Bool)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (node : Fin graph.decls.size) (polarity : Bool) :
    (compileAIGDualRailTrajectory technology graph assign initial node).ready polarity ≤
      (aigDualRailGraphDeadline technology graph).value := by
  rw [compileAIGDualRailTrajectory_ready_eq_source]
  exact aigDualRailReadyAt_le_graphDeadline technology graph node polarity

def aigDualRailSampledTime {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α)
    (clockSource : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) : SISecond :=
  finiteSamplingClockSampleTime clockSource code (aigDualRailGraphDeadline technology graph)

def aigDualRailClockTicks {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α)
    (clockSource : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) : Nat :=
  finiteSamplingClockTickCount clockSource code (aigDualRailGraphDeadline technology graph)

theorem aigDualRailSampledTime_eq_ticks {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α)
    (clockSource : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    (aigDualRailSampledTime technology graph clockSource code).value =
      (aigDualRailClockTicks technology graph clockSource code : ℝ) *
        (finiteSamplingClockTickPeriod clockSource code).value := rfl

theorem aigDualRailSampledTime_late {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α)
    (clockSource : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    (aigDualRailGraphDeadline technology graph).value ≤
      (aigDualRailSampledTime technology graph clockSource code).value :=
  finiteSamplingClock_requested_le_sampleTime clockSource code (aigDualRailGraphDeadline technology graph)

theorem compileAIGDualRailTrajectory_ready_le_sampledTime
    {α : Type} [DecidableEq α] [Hashable α]
    (technology : AIGCellTechnology) (graph : AIG α) (assign : α → Bool)
    (initial : Fin graph.decls.size → Bool → SIVolt)
    (clockSource : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (node : Fin graph.decls.size) (polarity : Bool) :
    (compileAIGDualRailTrajectory technology graph assign initial node).ready polarity ≤
      (aigDualRailSampledTime technology graph clockSource code).value :=
  (compileAIGDualRailTrajectory_ready_le_graphDeadline technology graph assign initial node polarity).trans
    (aigDualRailSampledTime_late technology graph clockSource code)

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
