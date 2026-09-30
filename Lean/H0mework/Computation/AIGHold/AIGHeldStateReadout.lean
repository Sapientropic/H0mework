import H0mework.Computation.AIGHold.AIGHeldState

/-! # Initial charge and held reads are projections of one complete physical bank state -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

noncomputable section

theorem aigBankHoldWave_before_capture
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (index : Fin width) (time : ℝ)
    (before : time ≤ (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value) :
    aigBankHoldWave technology entry input initial downstreamTechnology downstreamGraph first clock code index time =
      aigBankVoltage technology entry input initial index time := by
  apply SIQuantity.ext
  exact ClockedLeakyHoldSource.voltageAt_before
    (compileHoldLeaseForGraph (aigBankCell technology entry index) downstreamTechnology downstreamGraph clock code)
    _ _ time before

theorem aigHeldBankStateAt_output
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (index : Fin width) (time : ℝ) :
    aigHeldBankStateAt technology entry input initial downstreamTechnology downstreamGraph first clock code
      ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false time =
      aigBankHoldWave technology entry input initial downstreamTechnology downstreamGraph first clock code index time := by
  unfold aigHeldBankStateAt
  rw [dif_pos ⟨by
    change entry.aig.decls.size ≤ ((aigOutputBank entry).vec.get index.val index.isLt).gate
    rw [aigOutputBank_ref_gate]
    omega, rfl⟩]
  dsimp only
  apply congrArg (fun current : Fin width =>
    aigBankHoldWave technology entry input initial downstreamTechnology downstreamGraph first clock code current time)
  apply Fin.ext
  dsimp only
  simp only [aigOutputBank_ref_gate, Nat.add_sub_cancel_left]

theorem aigHeldBankStateAt_before_capture
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) (time : ℝ)
    (before : time ≤ (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value) :
    aigHeldBankStateAt technology entry input initial downstreamTechnology downstreamGraph
      first clock code node polarity time =
      (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig input initial node).wave polarity time := by
  unfold aigHeldBankStateAt
  split
  · rename_i held
    let index : Fin width := ⟨node.val - entry.aig.decls.size, by
      have bound := node.isLt
      have size := aigOutputBank_size entry
      omega⟩
    have address : (⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ : Fin (aigOutputBank entry).aig.decls.size) = node := by
      apply Fin.ext
      dsimp only
      rw [aigOutputBank_ref_gate]
      dsimp only [index]
      omega
    rw [aigBankHoldWave_before_capture technology entry input initial downstreamTechnology downstreamGraph
      first clock code _ time before]
    change (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig input initial
      ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩).wave false time = _
    rw [address, held.2]
  · rfl

theorem aigHeldBankStateAt_initial
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) :
    aigHeldBankStateAt technology entry input initial downstreamTechnology downstreamGraph
      first clock code node polarity 0 =
      match (aigOutputBank entry).aig.decls[node.val], polarity with
      | .false, false => ⟨0⟩
      | .false, true => technology.supply
      | .atom atom, false => input atom 0
      | _, _ => initial node polarity := by
  have captureNonnegative :
      0 ≤ (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value := by
    change 0 ≤ (finiteSamplingClockTickCount clock code _ : ℝ) *
      (finiteSamplingClockTickPeriod clock code).value
    exact mul_nonneg (Nat.cast_nonneg _) (finiteSamplingClockTickPeriod_pos clock code).le
  rw [aigHeldBankStateAt_before_capture technology entry input initial downstreamTechnology downstreamGraph
    first clock code node polarity 0 captureNonnegative]
  exact compileAIGDualRailTrajectoryFromInputs_initial technology (aigOutputBank entry).aig input initial node polarity

theorem aigBankHeldRead_eq_state_projection
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) :
    aigBankHeldRead technology entry input initial downstreamTechnology downstreamGraph first clock code =
      let stop := (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value
      let readTime := (aigInputSampledTime downstreamTechnology downstreamGraph stop clock code).value
      Vector.ofFn (fun index : Fin width => railRead? (aigBankCell technology entry index)
        (aigHeldBankStateAt technology entry input initial downstreamTechnology downstreamGraph first clock code
          ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
            ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false readTime)) := by
  dsimp only
  apply Vector.ext
  intro index bound
  simp only [aigBankHeldRead, Vector.getElem_ofFn, aigHeldBankStateAt_output]

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
