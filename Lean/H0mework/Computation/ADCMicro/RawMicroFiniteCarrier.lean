import H0mework.Computation.ADCMicro.RawMicroMachine
import H0mework.Computation.AIGExecution.AIGOwnedFiniteState
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option

/-!
# The actual raw microreceiver has a finite whole-state carrier

The descriptor below exists only to prove finiteness. It enumerates the data
already held by each actual runtime constructor and does not replace the
microstate, its step, or its source-generated execution horizon.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open Std.Sat
open Std.Tactic.BVDecide

noncomputable section

private noncomputable instance finiteArrayVector
    {α : Type} [Finite α] {n : Nat} : Finite (Vector α n) := by
  apply Finite.of_injective (fun values (index : Fin n) => values[index.val])
  intro left right same
  apply Vector.ext
  intro index bound
  exact congrFun same ⟨index, bound⟩

private abbrev FiniteADCChannelWord :=
  FiniteEmbodimentChannel → BitVec 128

private noncomputable instance finiteADCReceiverDifferenceRegistersFinite :
    Finite FiniteADCReceiverDifferenceRegisters := by
  let build :
      FiniteADCChannelWord × FiniteADCChannelWord ×
          FiniteADCChannelWord × FiniteADCChannelWord →
        FiniteADCReceiverDifferenceRegisters :=
    fun fields => ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  exact Finite.of_surjective build (by
    rintro ⟨resistorNumerator, resistorSpan, inductorNumerator, inductorSpan⟩
    exact ⟨(resistorNumerator, resistorSpan, inductorNumerator, inductorSpan), rfl⟩)

private noncomputable instance finiteADCReceiverSquareRegistersFinite :
    Finite FiniteADCReceiverSquareRegisters := by
  let build :
      FiniteADCChannelWord × FiniteADCChannelWord × FiniteADCChannelWord ×
          FiniteADCChannelWord × FiniteADCChannelWord × FiniteADCChannelWord →
        FiniteADCReceiverSquareRegisters :=
    fun fields =>
      ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
        fields.2.2.2.2.1, fields.2.2.2.2.2⟩
  exact Finite.of_surjective build (by
    rintro ⟨resistorSpan, inductorSpan, resistorNumeratorSquared,
      resistorSpanSquared, inductorNumeratorSquared, inductorSpanSquared⟩
    exact ⟨(resistorSpan, inductorSpan, resistorNumeratorSquared,
      resistorSpanSquared, inductorNumeratorSquared, inductorSpanSquared), rfl⟩)

private noncomputable instance finiteADCReceiverProductRegistersFinite :
    Finite FiniteADCReceiverProductRegisters := by
  let build :
      FiniteADCChannelWord × FiniteADCChannelWord × FiniteADCChannelWord ×
          FiniteADCChannelWord × FiniteADCChannelWord →
        FiniteADCReceiverProductRegisters :=
    fun fields =>
      ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2⟩
  exact Finite.of_surjective build (by
    rintro ⟨resistorSpan, inductorSpan, thresholdDenominator,
      resistorEnergyTerm, inductorEnergyTerm⟩
    exact ⟨(resistorSpan, inductorSpan, thresholdDenominator,
      resistorEnergyTerm, inductorEnergyTerm), rfl⟩)

private noncomputable instance finiteADCReceiverSumRegistersFinite :
    Finite FiniteADCReceiverSumRegisters := by
  let build :
      FiniteADCChannelWord × FiniteADCChannelWord ×
          FiniteADCChannelWord × FiniteADCChannelWord →
        FiniteADCReceiverSumRegisters :=
    fun fields => ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  exact Finite.of_surjective build (by
    rintro ⟨resistorSpan, inductorSpan, thresholdDenominator, energySum⟩
    exact ⟨(resistorSpan, inductorSpan, thresholdDenominator, energySum), rfl⟩)

private noncomputable instance finiteADCReceiverScaledRegistersFinite :
    Finite FiniteADCReceiverScaledRegisters := by
  let build :
      FiniteADCChannelWord × FiniteADCChannelWord ×
          FiniteADCChannelWord × FiniteADCChannelWord →
        FiniteADCReceiverScaledRegisters :=
    fun fields => ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  exact Finite.of_surjective build (by
    rintro ⟨resistorSpan, inductorSpan, thresholdDenominator, scaledEnergyNumerator⟩
    exact ⟨(resistorSpan, inductorSpan, thresholdDenominator, scaledEnergyNumerator), rfl⟩)

private noncomputable instance finiteADCRangeCheckedRawPacketForFinite
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat) :
    Finite (FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) := by
  apply Finite.of_injective FiniteADCRangeCheckedRawPacketFor.packet
  intro left right same
  cases left
  cases right
  cases same
  rfl

private abbrev FiniteADCRawMicroPacketDescriptor
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat)
    (packetGraph : AIG BVBit) :=
  Σ raw : FiniteADCWirePacketFor code counterBits,
    AIGOwnedProgress packetGraph
      (finiteADCRawPacketPhaseAssignment code lastTick raw)

private abbrev FiniteADCRawMicroCalibrationDescriptor
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat)
    (calibrationGraph : AIG BVBit) :=
  Σ checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick,
    AIGOwnedProgress calibrationGraph
      (finiteADCRawCalibrationPhaseAssignment checked)

private abbrev FiniteADCRawMicroDifferenceDescriptor
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat)
    (subGraph : AIG BVBit) :=
  Σ checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick,
    AIGOwnedBatch subGraph (finiteADCRawDifferencePhaseAssignments checked)

private abbrev FiniteADCRawMicroSquareDescriptor (mulGraph : AIG BVBit) :=
  Σ input : FiniteADCReceiverDifferenceRegisters,
    AIGOwnedBatch mulGraph (finiteADCRawSquarePhaseAssignments input)

private abbrev FiniteADCRawMicroProductDescriptor (mulGraph : AIG BVBit) :=
  Σ input : FiniteADCReceiverSquareRegisters,
    AIGOwnedBatch mulGraph (finiteADCRawProductPhaseAssignments input)

private abbrev FiniteADCRawMicroSumDescriptor (addGraph : AIG BVBit) :=
  Σ input : FiniteADCReceiverProductRegisters,
    AIGOwnedBatch addGraph (finiteADCRawSumPhaseAssignments input)

private abbrev FiniteADCRawMicroScaleDescriptor (mulGraph : AIG BVBit) :=
  Σ input : FiniteADCReceiverSumRegisters,
    AIGOwnedBatch mulGraph (finiteADCRawScalePhaseAssignments input)

private abbrev FiniteADCRawMicroCompareDescriptor
    (signedGraph unsignedGraph : AIG BVBit) :=
  Σ input : FiniteADCReceiverScaledRegisters,
    AIGOwnedBatch signedGraph (finiteADCRawSignedComparePhaseAssignments input) ×
      AIGOwnedBatch unsignedGraph (finiteADCRawUnsignedComparePhaseAssignments input)

private abbrev FiniteADCRawMicroFinalAndDescriptor (unsignedGraph : AIG BVBit) :=
  Σ _spanAnd : Vector Bool 10,
    Σ input : FiniteADCReceiverScaledRegisters,
      { unsignedCurrent : AIGOwnedBatch unsignedGraph
          (finiteADCRawUnsignedComparePhaseAssignments input) //
        unsignedGraph.decls.size ≤ unsignedCurrent.ticks }

private abbrev FiniteADCRawMicroStateDescriptor
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat)
    (packetGraph calibrationGraph subGraph mulGraph addGraph signedGraph unsignedGraph : AIG BVBit) :=
  ((FiniteADCRawMicroPacketDescriptor code counterBits lastTick packetGraph ⊕
      FiniteADCRawMicroCalibrationDescriptor code counterBits lastTick calibrationGraph) ⊕
    (FiniteADCRawMicroDifferenceDescriptor code counterBits lastTick subGraph ⊕
      FiniteADCRawMicroSquareDescriptor mulGraph)) ⊕
  (((FiniteADCRawMicroProductDescriptor mulGraph ⊕
      FiniteADCRawMicroSumDescriptor addGraph) ⊕
    (FiniteADCRawMicroScaleDescriptor mulGraph ⊕
      FiniteADCRawMicroCompareDescriptor signedGraph unsignedGraph)) ⊕
    (FiniteADCRawMicroFinalAndDescriptor unsignedGraph ⊕ Option (Vector Bool 10)))

private def finiteADCRawMicroStateOfDescriptor
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    {packetGraph calibrationGraph subGraph mulGraph addGraph signedGraph unsignedGraph : AIG BVBit} :
    FiniteADCRawMicroStateDescriptor code counterBits lastTick packetGraph calibrationGraph
        subGraph mulGraph addGraph signedGraph unsignedGraph →
      FiniteADCRawMicroStateAt code counterBits lastTick packetGraph calibrationGraph
        subGraph mulGraph addGraph signedGraph unsignedGraph
  | .inl (.inl (.inl ⟨raw, current⟩)) => .packet raw current
  | .inl (.inl (.inr ⟨checked, current⟩)) => .calibration checked current
  | .inl (.inr (.inl ⟨checked, current⟩)) => .difference checked current
  | .inl (.inr (.inr ⟨input, current⟩)) => .square input current
  | .inr (.inl (.inl (.inl ⟨input, current⟩))) => .product input current
  | .inr (.inl (.inl (.inr ⟨input, current⟩))) => .sum input current
  | .inr (.inl (.inr (.inl ⟨input, current⟩))) => .scale input current
  | .inr (.inl (.inr (.inr ⟨input, signedCurrent, unsignedCurrent⟩))) =>
      .compare input signedCurrent unsignedCurrent
  | .inr (.inr (.inl ⟨spanAnd, input, ⟨unsignedCurrent, complete⟩⟩)) =>
      .finalAnd spanAnd input unsignedCurrent complete
  | .inr (.inr (.inr result)) => .done result

private theorem finiteADCRawMicroStateOfDescriptor_surjective
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    {packetGraph calibrationGraph subGraph mulGraph addGraph signedGraph unsignedGraph : AIG BVBit} :
    Function.Surjective
      (@finiteADCRawMicroStateOfDescriptor code counterBits lastTick packetGraph calibrationGraph
        subGraph mulGraph addGraph signedGraph unsignedGraph) := by
  intro state
  cases state with
  | packet raw current => exact ⟨.inl (.inl (.inl ⟨raw, current⟩)), rfl⟩
  | calibration checked current => exact ⟨.inl (.inl (.inr ⟨checked, current⟩)), rfl⟩
  | difference checked current => exact ⟨.inl (.inr (.inl ⟨checked, current⟩)), rfl⟩
  | square input current => exact ⟨.inl (.inr (.inr ⟨input, current⟩)), rfl⟩
  | product input current => exact ⟨.inr (.inl (.inl (.inl ⟨input, current⟩))), rfl⟩
  | sum input current => exact ⟨.inr (.inl (.inl (.inr ⟨input, current⟩))), rfl⟩
  | scale input current => exact ⟨.inr (.inl (.inr (.inl ⟨input, current⟩))), rfl⟩
  | compare input signedCurrent unsignedCurrent =>
      exact ⟨.inr (.inl (.inr (.inr ⟨input, signedCurrent, unsignedCurrent⟩))), rfl⟩
  | finalAnd spanAnd input unsignedCurrent complete =>
      exact ⟨.inr (.inr (.inl ⟨spanAnd, input, ⟨unsignedCurrent, complete⟩⟩)), rfl⟩
  | done result => exact ⟨.inr (.inr (.inr result)), rfl⟩

/-- Every state of the actual graph-parametric microreceiver belongs to a
finite carrier. No graph is specialized or unfolded by this instance. -/
noncomputable instance finiteADCRawMicroStateAtFinite
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat)
    (packetGraph calibrationGraph subGraph mulGraph addGraph signedGraph unsignedGraph : AIG BVBit) :
    Finite (FiniteADCRawMicroStateAt code counterBits lastTick packetGraph calibrationGraph
      subGraph mulGraph addGraph signedGraph unsignedGraph) :=
  Finite.of_surjective finiteADCRawMicroStateOfDescriptor
    finiteADCRawMicroStateOfDescriptor_surjective

/-- The same generic instance applies to every source-owned installed program. -/
theorem finiteADCRawMicroStateWithProgram_finite
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (program : FiniteADCRawInstalledProgram code counterBits) (lastTick : Nat) :
    Finite (FiniteADCRawMicroStateWithProgram program lastTick) :=
  inferInstance

/-- Code-facing execution is the compiler specialization of the same finite carrier. -/
theorem finiteADCRawMicroStateFor_finite
    (code : FiniteADCResolutionCode) (counterBits lastTick : Nat) :
    Finite (FiniteADCRawMicroStateFor code counterBits lastTick) :=
  inferInstance

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
