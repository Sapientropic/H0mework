import H0mework.Fock.ReceivedStep.EncodingRecovery
import H0mework.Fock.ReceivedStep.NativeState

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

def advanceData (bound stride nextStride count : Nat) (selected : Bool)
    (previous : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) :
    (Fin ((bound + 2) * (nextStride + 1)) → ℚ) × ℚ × ℚ :=
  let fraction : ℚ := ((count + 1 : Nat) : ℚ)⁻¹
  let retained := fun position : Fin ((bound + 2) * (nextStride + 1)) => coordinateAt bound stride previous position.val
  if selected then
    (fun position => retained position + fraction * ((if position.val = bound + 2 then 1 else 0) - retained position),
      previous.2.1 + fraction * (1 - previous.2.1),
      previous.2.2 + fraction * ((bound + 3 : ℚ) - previous.2.2))
  else (retained, previous.2.1, previous.2.2)

def completeStep {Key : Type*} [DecidableEq Key] (bound stride nextStride : Nat) (nonunit : stride ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples bound (stride + 1)) (added key : Key) :
    (Fin ((bound + 2) * (nextStride + 1)) → ℚ) × ℚ × ℚ :=
  advanceData bound stride nextStride (receiveState bound stride nonunit received key).1 (decide (key = added))
    (SourceRationalWindowReadout.decode bound stride (received key))

def completeNextSamples {Key : Type*} [DecidableEq Key] (bound stride nextStride : Nat) (nonunit : stride ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples bound (stride + 1)) (added key : Key) :
    SourceRationalWindowReadout.Samples (bound + 1) (nextStride + 1) :=
  completeSamples (bound + 1) nextStride (completeStep bound stride nextStride nonunit received added key)

theorem unchanged_moments (bound stride nextStride count : Nat)
    (previous : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) :
    (advanceData bound stride nextStride count false previous).2 = previous.2 := rfl

theorem selected_mass (bound stride nextStride count : Nat)
    (previous : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) :
    (advanceData bound stride nextStride count true previous).2.1 =
      previous.2.1 + ((count + 1 : Nat) : ℚ)⁻¹ * (1 - previous.2.1) := rfl

theorem selected_clock (bound stride nextStride count : Nat)
    (previous : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) :
    (advanceData bound stride nextStride count true previous).2.2 =
      previous.2.2 + ((count + 1 : Nat) : ℚ)⁻¹ * ((bound + 3 : ℚ) - previous.2.2) := rfl

end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
