import H0mework.Computation.DualRailAIG.InputState
import H0mework.Computation.AIGHold.AIGBankReadout

/-! # The complete physical bank state includes its actually isolated output capacitors -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Set Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

/-- Appended output ports do not secretly remain controls of another internal gate. -/
theorem aigOutputBank_controls_are_old (entry : AIG.RefVecEntry α width)
    (node : Fin (aigOutputBank entry).aig.decls.size) (left right : AIG.Fanin)
    (selected : (aigOutputBank entry).aig.decls[node.val] = .gate left right) :
    left.gate < entry.aig.decls.size ∧ right.gate < entry.aig.decls.size := by
  by_cases old : node.val < entry.aig.decls.size
  · have earlier := (aigOutputBank entry).aig.hdag node.isLt selected
    exact ⟨earlier.1.trans old, earlier.2.trans old⟩
  · have bounded : node.val - entry.aig.decls.size < width := by
      have bound := node.isLt
      have size := aigOutputBank_size entry
      omega
    have added := aigOutputBankDecls_new entry ⟨node.val - entry.aig.decls.size, bounded⟩
    have address : entry.aig.decls.size + (node.val - entry.aig.decls.size) = node.val := by omega
    simp only [address] at added
    change (aigOutputBankDecls entry)[node.val] = .gate left right at selected
    rw [added] at selected
    obtain ⟨rfl, rfl⟩ := AIG.Decl.gate.inj selected
    simpa only [AIG.Fanin.gate_mk] using
      And.intro (entry.vec.get _ bounded).hgate entry.aig.hzero

theorem ClockedLeakyHoldSource.wave_mem_rail {source : LoadedConductanceCellSource}
    (hold : ClockedLeakyHoldSource source) (input : ℝ → SIVolt)
    (inputRail : ∀ t, 0 ≤ t → InRail source (input t))
    (stop time : ℝ) (stopNonnegative : 0 ≤ stop) (timeNonnegative : 0 ≤ time) :
    InRail source (hold.wave input stop time) := by
  by_cases before : time ≤ stop
  · change InRail source ⟨hold.voltageAt input stop time⟩
    rw [hold.voltageAt_before input stop time before]
    exact inputRail time timeNonnegative
  · have captured := inputRail stop stopNonnegative
    have decayPositive := Real.exp_pos (-(time - stop) / hold.timeConstant.value)
    have decayLe : Real.exp (-(time - stop) / hold.timeConstant.value) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hold.timeConstant_pos.le)
    change 0 ≤ hold.voltageAt input stop time ∧ hold.voltageAt input stop time ≤ source.supply.value
    rw [hold.voltageAt_after input stop time (le_of_not_ge before)]
    dsimp only [ClockedLeakyHoldSource.decayAt]
    exact ⟨mul_nonneg captured.1 decayPositive.le,
      (mul_le_of_le_one_right captured.1 decayLe).trans captured.2⟩

noncomputable section

def aigHeldBankStateAt (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (node : Fin (aigOutputBank entry).aig.decls.size) (polarity : Bool) (time : ℝ) : SIVolt :=
  if held : entry.aig.decls.size ≤ node.val ∧ polarity = false then
    have bounded : node.val - entry.aig.decls.size < width := by
      have bound := node.isLt
      have size := aigOutputBank_size entry
      omega
    aigBankHoldWave technology entry input initial downstreamTechnology downstreamGraph first clock code
      ⟨node.val - entry.aig.decls.size, bounded⟩ time
  else
    (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig input initial node).wave polarity time

theorem aigHeldBankStateAt_old
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (node : Fin (aigOutputBank entry).aig.decls.size) (old : node.val < entry.aig.decls.size)
    (polarity : Bool) (time : ℝ) :
    aigHeldBankStateAt technology entry input initial downstreamTechnology downstreamGraph
      first clock code node polarity time =
        (compileAIGDualRailTrajectoryFromInputs technology (aigOutputBank entry).aig input initial node).wave polarity time := by
  simp only [aigHeldBankStateAt, not_le_of_gt old, false_and, ↓reduceDIte]

theorem aigHeldBankStateAt_mem_rail
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology (aigOutputBank entry).aig node polarity) (initial node polarity))
    (inputContinuous : ∀ (node : Fin (aigOutputBank entry).aig.decls.size) atom,
      (aigOutputBank entry).aig.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))
    (inputRail : ∀ (node : Fin (aigOutputBank entry).aig.decls.size) atom,
      (aigOutputBank entry).aig.decls[node.val] = .atom atom → ∀ t, 0 ≤ t →
        InRail (compileDualRailCell technology (aigOutputBank entry).aig node false) (input atom t))
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (firstNonnegative : 0 ≤ first) (clock : ResonantDrivenCoreSource)
    (code : FiniteSamplingClockCode) (node : Fin (aigOutputBank entry).aig.decls.size)
    (polarity : Bool) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    InRail (compileDualRailCell technology (aigOutputBank entry).aig node polarity)
      (aigHeldBankStateAt technology entry input initial downstreamTechnology downstreamGraph
        first clock code node polarity time) := by
  unfold aigHeldBankStateAt
  split
  · rename_i held
    let index : Fin width := ⟨node.val - entry.aig.decls.size, by
      have bound := node.isLt
      have size := aigOutputBank_size entry
      omega⟩
    have bankRail : ∀ t, 0 ≤ t → InRail (aigBankCell technology entry index)
        (aigBankVoltage technology entry input initial index t) :=
      fun t ht => compileAIGDualRailTrajectoryFromInputs_mem_rail technology (aigOutputBank entry).aig
        input initial initialRail inputContinuous inputRail _ false t ht
    have stopNonnegative : 0 ≤ (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value := by
      have late := aigInputSampledTime_late technology (aigOutputBank entry).aig first clock code
      have delay := aigDualRailGraphDeadline_nonneg technology (aigOutputBank entry).aig
      linarith
    exact (compileHoldLeaseForGraph (aigBankCell technology entry index) downstreamTechnology downstreamGraph clock code).wave_mem_rail
      _ bankRail _ time stopNonnegative timeNonnegative
  · exact compileAIGDualRailTrajectoryFromInputs_mem_rail technology (aigOutputBank entry).aig
      input initial initialRail inputContinuous inputRail node polarity time timeNonnegative

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
