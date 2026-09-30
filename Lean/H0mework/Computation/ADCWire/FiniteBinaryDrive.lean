import H0mework.Physics.PortCoupling.Dynamics
import H0mework.Foundation.Relations.ConsumerQuotient

/-!
# Independently addressed binary source commands

Each input bit is a source-port actuation, declared before any ADC, endpoint
decoder, or coupling verdict. Uniform Boolean preparation is a special case;
single-channel commands implement the existing intervention primitive.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open NoIslandNoMagic.Consciousness.Representation

/-- Ten independently addressable source bits. -/
abbrev FiniteBinaryDrive := FiniteEmbodimentChannel → Bool

/-- Source-side addressed requests, independent of every candidate digital carrier. -/
def binaryDriveConsumers : IndependentConsumerSystem FiniteBinaryDrive where
  Consumer := FiniteEmbodimentChannel
  Output := fun _ => Bool
  read := fun channel drive => drive channel
  positive := ⟨.sourceBound⟩

theorem binaryDriveConsumers_indistinguishable_iff_eq (left right : FiniteBinaryDrive) :
    binaryDriveConsumers.Indistinguishable left right ↔ left = right := by
  constructor
  · intro same
    funext channel
    exact same channel
  · rintro rfl
    exact fun _ => rfl

/-- The legacy common-mode input. -/
def uniformBinaryDrive (phase : Bool) : FiniteBinaryDrive := fun _ => phase

/-- A source command that actuates exactly one registered channel. -/
def singleBinaryDrive (selected : FiniteEmbodimentChannel) : FiniteBinaryDrive :=
  fun channel => decide (channel = selected)

/-- Actual source and target preparation before the circuit executes. -/
def binaryDriveState (drive : FiniteBinaryDrive) : FiniteEmbodimentState :=
  fun channel => if drive channel then (1, 0) else (0, 0)

@[simp] theorem binaryDriveState_uniform (phase : Bool) :
    binaryDriveState (uniformBinaryDrive phase) = preparedState phase := rfl

@[simp] theorem binaryDriveState_single (selected : FiniteEmbodimentChannel) :
    binaryDriveState (singleBinaryDrive selected) = intervention selected 1 := by
  funext channel
  by_cases same : channel = selected
  · simp [binaryDriveState, singleBinaryDrive, intervention, same]
  · simp [binaryDriveState, singleBinaryDrive, intervention, same]

@[simp] theorem binaryDriveState_target (drive : FiniteBinaryDrive)
    (channel : FiniteEmbodimentChannel) :
    targetPort (binaryDriveState drive) channel = 0 := by
  cases h : drive channel <;> simp [binaryDriveState, targetPort, h]

@[simp] theorem binaryDriveState_source (drive : FiniteBinaryDrive)
    (channel : FiniteEmbodimentChannel) :
    sourcePort (binaryDriveState drive) channel = if drive channel then 1 else 0 := by
  cases h : drive channel <;> simp [binaryDriveState, sourcePort, h]

theorem binaryDriveState_injective : Function.Injective binaryDriveState := by
  intro left right same
  funext channel
  have coordinate := congrArg (fun state => sourcePort state channel) same
  simp only [binaryDriveState_source] at coordinate
  cases hl : left channel <;> cases hr : right channel <;>
    simp [hl, hr] at coordinate ⊢

theorem finiteBinaryDrive_card : Fintype.card FiniteBinaryDrive = 1024 := by
  rw [Fintype.card_fun]
  simp [channel_cardinality]

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
