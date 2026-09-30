import H0mework.Computation.ADCGates.RawAdmissionGate

/-! # The complete finite raw-receiver dataflow, before any input packet exists -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface Std.Tactic.BVDecide

def receiverDataflowWord (code : FiniteADCResolutionCode) (address : FiniteADCRawWordAddress) : BVExpr 128 :=
  .extract 0 128 (.var (finiteADCRawAdmissionWordVariable address) : BVExpr (adcWordBits code))

def receiverDataflowSubtract (left right : BVExpr 128) : BVExpr 128 :=
  .bin left .add (.bin (.un .not right) .add (.const (BitVec.ofNat 128 1)))

def receiverDataflowDifference (code : FiniteADCResolutionCode) (frame : FiniteAffineMeterFrame)
    (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) : BVExpr 128 :=
  receiverDataflowSubtract (receiverDataflowWord code ((frame, leg), channel))
    (receiverDataflowWord code ((.zeroReference, leg), channel))

def receiverDataflowSquare (value : BVExpr 128) : BVExpr 128 := .bin value .mul value

def receiverDataflowDenominator (code : FiniteADCResolutionCode) (channel : FiniteEmbodimentChannel) : BVExpr 128 :=
  .bin (receiverDataflowSquare (receiverDataflowDifference code .spanReference .resistor channel)) .mul
    (receiverDataflowSquare (receiverDataflowDifference code .spanReference .inductor channel))

def receiverDataflowEnergyTerm (code : FiniteADCResolutionCode) (leg other : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : BVExpr 128 :=
  .bin (receiverDataflowSquare (receiverDataflowDifference code .operational leg channel)) .mul
    (receiverDataflowSquare (receiverDataflowDifference code .spanReference other channel))

def receiverDataflowScaledEnergy (code : FiniteADCResolutionCode) (channel : FiniteEmbodimentChannel) : BVExpr 128 :=
  .bin (.const (BitVec.ofNat 128 4)) .mul
    (.bin (receiverDataflowEnergyTerm code .resistor .inductor channel) .add
      (receiverDataflowEnergyTerm code .inductor .resistor channel))

def receiverDataflowSignedLt (left right : BVExpr 128) : BVLogicalExpr :=
  .gate .xor (.gate .xor (.literal (.getLsbD left 127)) (.literal (.getLsbD right 127)))
    (.literal (.bin left .ult right))

def receiverDataflowChannel (code : FiniteADCResolutionCode) (channel : FiniteEmbodimentChannel) : BVLogicalExpr :=
  .gate .and
    (.gate .and
      (receiverDataflowSignedLt (.const 0) (receiverDataflowDifference code .spanReference .resistor channel))
      (receiverDataflowSignedLt (.const 0) (receiverDataflowDifference code .spanReference .inductor channel)))
    (.literal (.bin (receiverDataflowDenominator code channel) .ult (receiverDataflowScaledEnergy code channel)))

/-- One validity port and ten independent channel ports share the original 62 input variables. -/
def receiverDataflowOutputs (code : FiniteADCResolutionCode) (counterBits : Nat) : Vector BVLogicalExpr 11 :=
  Vector.ofFn fun index =>
    if first : index.val = 0 then finiteADCRawAdmissionExpr code counterBits
    else receiverDataflowChannel code (finiteADCChannelEquivFin.symm ⟨index.val - 1, by omega⟩)

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
