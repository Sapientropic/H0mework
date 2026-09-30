import H0mework.Computation.AIGHold.AIGBankCapture
import H0mework.Computation.AIGHold.HoldLeaseDesign
import H0mework.Computation.AIGHold.ClockedLeakyHoldRetention

/-! # A single word graph generates distinct held ports with one common voltage lease -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Set Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

noncomputable section

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

def aigBankHoldWave (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (input : α → ℝ → SIVolt) (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (index : Fin width) : ℝ → SIVolt :=
  (compileHoldLeaseForGraph (aigBankCell technology entry index) downstreamTechnology downstreamGraph clock code).wave
    (aigBankVoltage technology entry input initial index)
    (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value

theorem aigBankHoldWave_window
    (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width) (input : α → ℝ → SIVolt)
    (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology (aigOutputBank entry).aig node polarity) (initial node polarity))
    (inputContinuous : ∀ (node : Fin (aigOutputBank entry).aig.decls.size) atom,
      (aigOutputBank entry).aig.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))
    (assign : α → Bool) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (inputBands : ∀ (node : Fin (aigOutputBank entry).aig.decls.size) atom,
      (aigOutputBank entry).aig.decls[node.val] = .atom atom → ∀ t ∈ Icc first last,
        BitBand (compileDualRailCell technology (aigOutputBank entry).aig node false) (assign atom) (input atom t))
    (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
    (leaseCoversCapture : (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value ≤ last)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) (index : Fin width) :
    let stop := (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value
    CellRailWindow (aigBankCell technology entry index)
      (AIG.denote assign ⟨entry.aig, entry.vec.get index.val index.isLt⟩)
      (aigBankHoldWave technology entry input initial downstreamTechnology downstreamGraph first clock code index)
      stop (stop + ((aigDualRailGraphDeadline downstreamTechnology downstreamGraph).value +
        (finiteSamplingClockTickPeriod clock code).value)) := by
  dsimp only
  have capture := aigBankVoltage_capture technology entry input initial initialRail inputContinuous
    assign first last firstNonnegative inputBands clock code leaseCoversCapture index
  have prior := compileAIGDualRailTrajectoryFromInputs_window technology (aigOutputBank entry).aig
    input initial initialRail inputContinuous assign first last firstNonnegative inputBands
    ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
      ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false
  let stop := (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value
  let hold := compileHoldLeaseForGraph (aigBankCell technology entry index)
    downstreamTechnology downstreamGraph clock code
  refine ⟨?_, hold.voltageAt_continuous _ prior.continuous stop, ?_⟩
  · have late := aigInputSampledTime_late technology (aigOutputBank entry).aig first clock code
    have delay := aigDualRailGraphDeadline_nonneg technology (aigOutputBank entry).aig
    linarith
  · intro t ht
    have within : t - stop ≤ hold.retentionTime.value := by
      rw [compileHoldLeaseForGraph_retentionTime]
      linarith [ht.2]
    have held := hold.retains_captureBand (aigBankVoltage technology entry input initial index) stop
      (AIG.denote assign ⟨entry.aig, entry.vec.get index.val index.isLt⟩) capture (t - stop)
      (by linarith [ht.1]) within
    have joined : stop + (t - stop) = t := by ring
    rw [joined] at held
    exact held

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
