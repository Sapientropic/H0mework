import Lean.Data.RArray
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.IntervalCases
import H0mework.Computation.ADCWire.WirePacket
import H0mework.Computation.AIGExecution.AIGExecutionSource
import Std.Tactic.BVDecide.Bitblast.BVExpr

/-!
# Fixed AIG for raw ADC packet admission

The static graph depends only on ADC resolution and counter width. Runtime
assignment supplies a clamped clock bound, one header, and sixty raw words.
The graph contains eighty-one independent predicates: one header bound, sixty
raw-code bounds, and twenty positive-span comparisons. It contains no desired
accept bit, decoded sample, physical target, or source correctness witness.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision
open Std.Sat
open Std.Tactic.BVDecide

abbrev FiniteADCRawWordAddress :=
  (FiniteAffineMeterFrame × SynchronousSenseLeg) × FiniteEmbodimentChannel

abbrev FiniteADCRawSpanAddress := SynchronousSenseLeg × FiniteEmbodimentChannel

def finiteADCFrameEquivFin : FiniteAffineMeterFrame ≃ Fin 3 where
  toFun
    | .zeroReference => 0
    | .spanReference => 1
    | .operational => 2
  invFun index := match index.val with
    | 0 => .zeroReference
    | 1 => .spanReference
    | _ => .operational
  left_inv := by intro frame; cases frame <;> rfl
  right_inv := by intro index; rcases index with ⟨index, bound⟩; interval_cases index <;> rfl

def finiteADCLegEquivFin : SynchronousSenseLeg ≃ Fin 2 where
  toFun
    | .resistor => 0
    | .inductor => 1
  invFun index := match index.val with
    | 0 => .resistor
    | _ => .inductor
  left_inv := by intro leg; cases leg <;> rfl
  right_inv := by intro index; rcases index with ⟨index, bound⟩; interval_cases index <;> rfl

def finiteADCChannelEquivFin : FiniteEmbodimentChannel ≃ Fin 10 where
  toFun
    | .sourceBound => 0
    | .machineToNeuralWrite => 1
    | .neuralToMachineReceipt => 2
    | .neuralToBodyEffect => 3
    | .bodyToNeuralFeedback => 4
    | .learnedStateTrace => 5
    | .recursiveSelfWriteBack => 6
    | .generatedNext => 7
    | .authorityAndRefusalSettlement => 8
    | .noPowerMinting => 9
  invFun index := match index.val with
    | 0 => .sourceBound
    | 1 => .machineToNeuralWrite
    | 2 => .neuralToMachineReceipt
    | 3 => .neuralToBodyEffect
    | 4 => .bodyToNeuralFeedback
    | 5 => .learnedStateTrace
    | 6 => .recursiveSelfWriteBack
    | 7 => .generatedNext
    | 8 => .authorityAndRefusalSettlement
    | _ => .noPowerMinting
  left_inv := by intro channel; cases channel <;> rfl
  right_inv := by intro index; rcases index with ⟨index, bound⟩; interval_cases index <;> rfl

def finiteADCRawWordAddressEquivFin : FiniteADCRawWordAddress ≃ Fin 60 :=
  ((finiteADCFrameEquivFin.prodCongr finiteADCLegEquivFin).prodCongr
      finiteADCChannelEquivFin).trans
    ((finProdFinEquiv.prodCongr (Equiv.refl (Fin 10))).trans finProdFinEquiv)

def finiteADCRawSpanAddressEquivFin : FiniteADCRawSpanAddress ≃ Fin 20 :=
  (finiteADCLegEquivFin.prodCongr finiteADCChannelEquivFin).trans finProdFinEquiv

/-- Total finite encoding of an arbitrary runtime upper bound. -/
def finiteADCRawAdmissionClampedLastTick
    (counterBits lastTick : Nat) : QuantizedWord counterBits :=
  ⟨min lastTick (2 ^ counterBits - 1), by
    have positive := Nat.two_pow_pos counterBits
    omega⟩

/-- The greatest admitted raw offset-binary word at each resolution. -/
def finiteADCValidRawMaximum
    (code : FiniteADCResolutionCode) : QuantizedWord (adcWordBits code) :=
  ⟨(32 * finiteADCGridDenominator code).toNat, by
    cases code <;> norm_num [finiteADCGridDenominator, adcWordBits]⟩

/-- Minimal runtime gate input. The full physical source is absent. -/
structure FiniteADCRawAdmissionInput
    (code : FiniteADCResolutionCode) (counterBits : Nat) where
  packetTick : QuantizedWord counterBits
  lastTickBound : QuantizedWord counterBits
  rawWordAt : FiniteAffineMeterFrame → SynchronousSenseLeg →
    FiniteEmbodimentChannel → QuantizedWord (adcWordBits code)

def FiniteADCRawAdmissionInput.packetAccepted
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) : Prop :=
  input.packetTick.val ≤ input.lastTickBound.val ∧
    ∀ address : FiniteADCRawWordAddress,
      validADCWord code (input.rawWordAt address.1.1 address.1.2 address.2)

def FiniteADCRawAdmissionInput.calibrationAccepted
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) : Prop :=
  ∀ address : FiniteADCRawSpanAddress,
    (input.rawWordAt .zeroReference address.1 address.2).val <
      (input.rawWordAt .spanReference address.1 address.2).val

def FiniteADCRawAdmissionInput.accepted
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) : Prop :=
  input.packetAccepted ∧ input.calibrationAccepted

/-- Build the runtime input without carrying the physical source into the digital program. -/
def finiteADCRawAdmissionInputOfPacketFor (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) :
    FiniteADCRawAdmissionInput code counterBits where
  packetTick := packet.1
  lastTickBound := finiteADCRawAdmissionClampedLastTick counterBits lastTick
  rawWordAt := packet.2

def finiteADCRawAdmissionInputOfPacket
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    FiniteADCRawAdmissionInput source.adcCode counterBits :=
  finiteADCRawAdmissionInputOfPacketFor source.adcCode lastTick packet

def finiteADCRawAdmissionWordVariable (address : FiniteADCRawWordAddress) : Nat :=
  2 + (finiteADCRawWordAddressEquivFin address).val

def finiteADCRawAdmissionPackedVariable
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits)
    (index : Fin 62) : BVExpr.PackedBitVec :=
  if zero : index.val = 0 then
    { bv := BitVec.ofFin input.packetTick }
  else if one : index.val = 1 then
    { bv := BitVec.ofFin input.lastTickBound }
  else
    let wordIndex : Fin 60 := ⟨index.val - 2, by omega⟩
    let address := finiteADCRawWordAddressEquivFin.symm wordIndex
    { bv := BitVec.ofFin (input.rawWordAt address.1.1 address.1.2 address.2) }

theorem finiteADCRawAdmissionVariableCount_pos : 0 < 62 := by decide

def finiteADCRawAdmissionAssignment
    {code : FiniteADCResolutionCode} {counterBits : Nat}
    (input : FiniteADCRawAdmissionInput code counterBits) : BVExpr.Assignment :=
  Lean.RArray.ofFn (finiteADCRawAdmissionPackedVariable input)
    finiteADCRawAdmissionVariableCount_pos

def finiteADCRawAdmissionAnd : List BVLogicalExpr → BVLogicalExpr
  | [] => .const true
  | predicate :: rest => .gate .and predicate (finiteADCRawAdmissionAnd rest)

def finiteADCRawAdmissionHeaderExpr (counterBits : Nat) : BVLogicalExpr :=
  .not (.literal (.bin (.var 1 : BVExpr counterBits) .ult
    (.var 0 : BVExpr counterBits)))

def finiteADCRawAdmissionWordExpr
    (code : FiniteADCResolutionCode) (address : FiniteADCRawWordAddress) : BVLogicalExpr :=
  .not (.literal (.bin
    (.const (BitVec.ofFin (finiteADCValidRawMaximum code))) .ult
    (.var (finiteADCRawAdmissionWordVariable address) : BVExpr (adcWordBits code))))

def finiteADCRawAdmissionSpanExpr
    (code : FiniteADCResolutionCode) (address : FiniteADCRawSpanAddress) : BVLogicalExpr :=
  .literal (.bin
    (.var (finiteADCRawAdmissionWordVariable ((.zeroReference, address.1), address.2)) :
      BVExpr (adcWordBits code)) .ult
    (.var (finiteADCRawAdmissionWordVariable ((.spanReference, address.1), address.2)) :
      BVExpr (adcWordBits code)))

/-- Header and all sixty raw-word range predicates. -/
def finiteADCRawPacketPredicates
    (code : FiniteADCResolutionCode) (counterBits : Nat) : List BVLogicalExpr :=
  finiteADCRawAdmissionHeaderExpr counterBits ::
    List.ofFn (fun index : Fin 60 => finiteADCRawAdmissionWordExpr code
      (finiteADCRawWordAddressEquivFin.symm index))

/-- All twenty raw positive-span predicates. -/
def finiteADCRawCalibrationPredicates
    (code : FiniteADCResolutionCode) : List BVLogicalExpr :=
  List.ofFn (fun index : Fin 20 => finiteADCRawAdmissionSpanExpr code
    (finiteADCRawSpanAddressEquivFin.symm index))

/-- Exactly one header, sixty validity, and twenty span predicates. -/
def finiteADCRawAdmissionPredicates
    (code : FiniteADCResolutionCode) (counterBits : Nat) : List BVLogicalExpr :=
  finiteADCRawPacketPredicates code counterBits ++ finiteADCRawCalibrationPredicates code

def finiteADCRawPacketExpr
    (code : FiniteADCResolutionCode) (counterBits : Nat) : BVLogicalExpr :=
  finiteADCRawAdmissionAnd (finiteADCRawPacketPredicates code counterBits)

def finiteADCRawCalibrationExpr (code : FiniteADCResolutionCode) : BVLogicalExpr :=
  finiteADCRawAdmissionAnd (finiteADCRawCalibrationPredicates code)

def finiteADCRawAdmissionExpr
    (code : FiniteADCResolutionCode) (counterBits : Nat) : BVLogicalExpr :=
  finiteADCRawAdmissionAnd (finiteADCRawAdmissionPredicates code counterBits)

/-- Fixed graph: runtime packet, bound, and acceptance are not compiler inputs. -/
def finiteADCRawPacketGraph
    (code : FiniteADCResolutionCode) (counterBits : Nat) : AIG.Entrypoint BVBit :=
  BVLogicalExpr.bitblast (finiteADCRawPacketExpr code counterBits)

def finiteADCRawCalibrationGraph
    (code : FiniteADCResolutionCode) : AIG.Entrypoint BVBit :=
  BVLogicalExpr.bitblast (finiteADCRawCalibrationExpr code)

def finiteADCRawAdmissionGraph
    (code : FiniteADCResolutionCode) (counterBits : Nat) : AIG.Entrypoint BVBit :=
  BVLogicalExpr.bitblast (finiteADCRawAdmissionExpr code counterBits)

/-- Processing length is the actual number of declarations in the generated graph. -/
def finiteADCRawAdmissionGateTicks
    (code : FiniteADCResolutionCode) (counterBits : Nat) : Nat :=
  (finiteADCRawAdmissionGraph code counterBits).aig.decls.size

def finiteADCRawPacketGateTicks
    (code : FiniteADCResolutionCode) (counterBits : Nat) : Nat :=
  (finiteADCRawPacketGraph code counterBits).aig.decls.size

def finiteADCRawCalibrationGateTicks (code : FiniteADCResolutionCode) : Nat :=
  (finiteADCRawCalibrationGraph code).aig.decls.size

/-- Execute the existing packet graph using only the finite ADC configuration and raw input. -/
def finiteADCRawPacketGateRunFor (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) : Bool :=
  let input := finiteADCRawAdmissionInputOfPacketFor code lastTick packet
  let graph := finiteADCRawPacketGraph code counterBits
  aigExecutionRead (finiteADCRawAdmissionAssignment input).toAIGAssignment graph.ref

def finiteADCRawCalibrationGateRunFor (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) : Bool :=
  let input := finiteADCRawAdmissionInputOfPacketFor code lastTick packet
  let graph := finiteADCRawCalibrationGraph code
  aigExecutionRead (finiteADCRawAdmissionAssignment input).toAIGAssignment graph.ref

/-- Execute the cached declaration table and read the graph's terminal reference. -/
def finiteADCRawAdmissionGateRunFor (code : FiniteADCResolutionCode)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketFor code counterBits) : Bool :=
  let input := finiteADCRawAdmissionInputOfPacketFor code lastTick packet
  let graph := finiteADCRawAdmissionGraph code counterBits
  aigExecutionRead (finiteADCRawAdmissionAssignment input).toAIGAssignment graph.ref

/-- The physical entry retains exactly the source's ADC restriction of the one digital executor. -/
def finiteADCRawPacketGateRun
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) : Bool :=
  finiteADCRawPacketGateRunFor source.adcCode lastTick packet

def finiteADCRawCalibrationGateRun
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) : Bool :=
  finiteADCRawCalibrationGateRunFor source.adcCode lastTick packet

def finiteADCRawAdmissionGateRun
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) : Bool :=
  finiteADCRawAdmissionGateRunFor source.adcCode lastTick packet

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
