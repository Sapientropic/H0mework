import H0mework.Computation.AIGHold.AIGBankHold

/-! # One simultaneous voltage read consumes the complete held word bank -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Set Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

noncomputable section

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

def aigBankHeldRead (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
    (input : α → ℝ → SIVolt) (initial : Fin (aigOutputBank entry).aig.decls.size → Bool → SIVolt)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
    (first : ℝ) (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode) : Vector (Option Bool) width :=
  let stop := (aigInputSampledTime technology (aigOutputBank entry).aig first clock code).value
  let sample := (aigInputSampledTime downstreamTechnology downstreamGraph stop clock code).value
  Vector.ofFn fun index => railRead? (aigBankCell technology entry index)
    (aigBankHoldWave technology entry input initial downstreamTechnology downstreamGraph first clock code index sample)

theorem aigBankHeldRead_eq_denote
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
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    aigBankHeldRead technology entry input initial downstreamTechnology downstreamGraph first clock code =
      Vector.ofFn (fun index : Fin width => some (AIG.denote assign ⟨entry.aig, entry.vec.get index.val index.isLt⟩)) := by
  apply Vector.ext
  intro index bounded
  simp only [aigBankHeldRead, Vector.getElem_ofFn]
  have held := aigBankHoldWave_window technology entry input initial initialRail inputContinuous assign
    first last firstNonnegative inputBands clock code leaseCoversCapture downstreamTechnology downstreamGraph ⟨index, bounded⟩
  have sampled := compileHoldLeaseForGraph_sample_mem_lease (aigBankCell technology entry ⟨index, bounded⟩)
    downstreamTechnology downstreamGraph clock code _ held.ready_nonneg
  rw [compileHoldLeaseForGraph_retentionTime] at sampled
  have band := held.settled _ sampled
  cases result : AIG.denote assign ⟨entry.aig, entry.vec.get index bounded⟩
  · exact railRead?_of_low _ _ (by simpa only [result, BitBand, Bool.false_eq_true, ↓reduceIte] using band)
  · exact railRead?_of_high _ _ (by simpa only [result, BitBand, ↓reduceIte] using band)

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
