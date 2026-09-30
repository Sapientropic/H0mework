import H0mework.Computation.WholeReceiver.GraphSource
import H0mework.Computation.WholeReceiver.DataflowSemantics
import H0mework.Computation.ADCMicro.RawMicroCorrectness

/-! # The whole source graph consumes the original receiver, including both rejection branches -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface Std.Sat Std.Tactic.BVDecide

theorem receiverWholeGraph_valid
    (code : FiniteADCResolutionCode) {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    (receiverWholeGraphRead (receiverWholeGraph code counterBits)
      (finiteADCRawAdmissionInputOfPacketFor code lastTick packet))[0] =
      (finiteADCRawPacketGateRunFor code lastTick packet && finiteADCRawCalibrationGateRunFor code lastTick packet) := by
  have output := receiverWholeGraphRead_compiled
    (finiteADCRawAdmissionInputOfPacketFor code lastTick packet) (0 : Fin 11)
  simp only [receiverDataflowOutputs, Vector.getElem_ofFn] at output
  exact output.trans (finiteADCRawAdmissionEval_eq_runs code lastTick packet)

theorem receiverWholeGraph_channel
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) (channel : FiniteEmbodimentChannel) :
    (receiverWholeGraphRead (receiverWholeGraph code counterBits)
      (finiteADCRawAdmissionInputOfPacketFor code lastTick checked.packet))[(finiteADCChannelEquivFin channel).val + 1] =
      finiteADCRawMicroDifferenceResult (finiteADCRawDifferenceRegistersFor checked) channel := by
  have output := receiverWholeGraphRead_compiled
    (finiteADCRawAdmissionInputOfPacketFor code lastTick checked.packet)
    (⟨(finiteADCChannelEquivFin channel).val + 1, by have := (finiteADCChannelEquivFin channel).isLt; omega⟩ : Fin 11)
  simp [receiverDataflowOutputs] at output
  exact output.trans (receiverDataflowChannel_eq_scaledDecision checked channel)

theorem receiverWholeDecode_eq_original
    (code : FiniteADCResolutionCode) {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    (receiverWholeDecode (receiverWholeGraphRead (receiverWholeGraph code counterBits)
      (finiteADCRawAdmissionInputOfPacketFor code lastTick packet))).map finiteADCRawBooleanReadout =
      finiteADCRawMicroPacketResultFor code lastTick packet := by
  unfold receiverWholeDecode
  rw [receiverWholeGraph_valid]
  by_cases accepted : finiteADCRawPacketGateRunFor code lastTick packet = true
  · by_cases calibrated : finiteADCRawCalibrationGateRunFor code lastTick packet = true
    · simp only [accepted, calibrated, Bool.and_self, ↓reduceIte, Option.map_some,
        finiteADCRawMicroPacketResultFor, ↓reduceDIte, finiteADCRawMicroCheckedResultFor]
      apply congrArg some
      funext channel
      simp only [finiteADCRawBooleanReadout, Vector.getElem_ofFn]
      exact receiverWholeGraph_channel (⟨packet, accepted⟩ : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) channel
    · simp [accepted, calibrated, finiteADCRawMicroPacketResultFor, finiteADCRawMicroCheckedResultFor]
  · simp [accepted, finiteADCRawMicroPacketResultFor]

theorem receiverWholeDecode_eq_microExecute
    (code : FiniteADCResolutionCode) {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    some ((receiverWholeDecode (receiverWholeGraphRead (receiverWholeGraph code counterBits)
      (finiteADCRawAdmissionInputOfPacketFor code lastTick packet))).map finiteADCRawBooleanReadout) =
      finiteADCRawMicroOutput (finiteADCRawMicroExecuteFor code lastTick packet) := by
  rw [receiverWholeDecode_eq_original, finiteADCRawMicroExecuteFor_completed]

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
