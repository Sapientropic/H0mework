import H0mework.Computation.WholeReceiver.Semantics
import H0mework.Computation.AIGHold.AIGBankReadout
import Init.Data.Vector.Monadic

/-! # The complete receiver is read from its own coupled and held physical graph -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Set Cells.Conductance Cells.Storage

/-- Unclassified voltage and a classified rejected packet remain different outcomes. -/
def receiverWholePhysicalDecode (outputs : Vector (Option Bool) 11) : Option (Option (Vector Bool 10)) :=
  (outputs.mapM id).map receiverWholeDecode

theorem receiverWholePhysicalDecode_map_some (outputs : Vector Bool 11) :
    receiverWholePhysicalDecode (outputs.map some) = some (receiverWholeDecode outputs) := by
  unfold receiverWholePhysicalDecode
  rw [Vector.mapM_map]
  have collected : outputs.mapM (m := Option) some = some outputs := by
    simpa only [id_eq, Vector.map_id, Option.pure_def] using
      (Vector.mapM_pure (m := Option) (xs := outputs) id)
  simp only [Function.comp_def, id_eq, collected, Option.map_some]

theorem receiverWholeHeldBank_eq_read
    {β : Type} [DecidableEq β] [Hashable β]
    (code : FiniteADCResolutionCode) (counterBits : Nat)
    (technology : AIGCellTechnology) (input : BVBit → ℝ → SIVolt)
    (initial : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology (aigOutputBank (receiverWholeGraph code counterBits)).aig node polarity)
        (initial node polarity))
    (inputContinuous : ∀ (node : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size) atom,
      (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls[node.val] = .atom atom →
        Continuous (fun t => (input atom t).value))
    (raw : FiniteADCRawAdmissionInput code counterBits) (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (inputBands : ∀ (node : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size) atom,
      (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls[node.val] = .atom atom → ∀ t ∈ Icc first last,
        BitBand (compileDualRailCell technology (aigOutputBank (receiverWholeGraph code counterBits)).aig node false)
          ((finiteADCRawAdmissionAssignment raw).toAIGAssignment atom) (input atom t))
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode)
    (leaseCoversCapture :
      (aigInputSampledTime technology (aigOutputBank (receiverWholeGraph code counterBits)).aig first clock clockCode).value ≤ last)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    aigBankHeldRead technology (receiverWholeGraph code counterBits) input initial
        downstreamTechnology downstreamGraph first clock clockCode =
      (receiverWholeGraphRead (receiverWholeGraph code counterBits) raw).map some := by
  rw [aigBankHeldRead_eq_denote technology (receiverWholeGraph code counterBits) input initial
    initialRail inputContinuous (finiteADCRawAdmissionAssignment raw).toAIGAssignment first last firstNonnegative inputBands
    clock clockCode leaseCoversCapture downstreamTechnology downstreamGraph]
  apply Vector.ext
  intro index bounded
  simp only [Vector.getElem_ofFn, Vector.getElem_map]
  rw [receiverWholeGraphRead_get _ raw (⟨index, bounded⟩ : Fin 11)]

theorem receiverWholePhysical_eq_microExecute
    {β : Type} [DecidableEq β] [Hashable β]
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat) (packet : FiniteADCWirePacketFor code counterBits)
    (technology : AIGCellTechnology) (input : BVBit → ℝ → SIVolt)
    (initial : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size → Bool → SIVolt)
    (initialRail : ∀ node polarity,
      InRail (compileDualRailCell technology (aigOutputBank (receiverWholeGraph code counterBits)).aig node polarity)
        (initial node polarity))
    (inputContinuous : ∀ (node : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size) atom,
      (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls[node.val] = .atom atom →
        Continuous (fun t => (input atom t).value))
    (first last : ℝ) (firstNonnegative : 0 ≤ first)
    (inputBands : ∀ (node : Fin (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls.size) atom,
      (aigOutputBank (receiverWholeGraph code counterBits)).aig.decls[node.val] = .atom atom → ∀ t ∈ Icc first last,
        BitBand (compileDualRailCell technology (aigOutputBank (receiverWholeGraph code counterBits)).aig node false)
          ((finiteADCRawAdmissionAssignment (finiteADCRawAdmissionInputOfPacketFor code lastTick packet)).toAIGAssignment atom)
          (input atom t))
    (clock : ResonantDrivenCoreSource) (clockCode : FiniteSamplingClockCode)
    (leaseCoversCapture :
      (aigInputSampledTime technology (aigOutputBank (receiverWholeGraph code counterBits)).aig first clock clockCode).value ≤ last)
    (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β) :
    (receiverWholePhysicalDecode (aigBankHeldRead technology (receiverWholeGraph code counterBits) input initial
        downstreamTechnology downstreamGraph first clock clockCode)).map (Option.map finiteADCRawBooleanReadout) =
      finiteADCRawMicroOutput (finiteADCRawMicroExecuteFor code lastTick packet) := by
  rw [receiverWholeHeldBank_eq_read code counterBits technology input initial initialRail inputContinuous
    (finiteADCRawAdmissionInputOfPacketFor code lastTick packet) first last firstNonnegative inputBands
    clock clockCode leaseCoversCapture downstreamTechnology downstreamGraph,
    receiverWholePhysicalDecode_map_some, Option.map_some]
  exact receiverWholeDecode_eq_microExecute code lastTick packet

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
