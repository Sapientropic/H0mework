import H0mework.Physics.MotherProgrammesFormationCurrent.Coordinates
import H0mework.Physics.MotherLaws.PointwiseRestriction

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRawCurrent

open CurrentMaterial StageNineCanonicalCauchyState MotherStreamLaws

noncomputable section

@[instance_reducible] def channelCodec : Encodable Channel := Encodable.ofCountable Channel
local instance instEncodableChannel_scratch : Encodable Channel := channelCodec

abbrev Input := StageNineSpatialPoint × Channel

/-- Every actual real spatial point enters the fixed evaluator input. -/
def inputSamples (input : Input) : Stream
  | 0 => (Encodable.encode input.2 : ℝ)
  | index + 1 => if bound : index < 3 then input.1 ⟨index, bound⟩ else 0

def inputRead (raw : Stream) : Input :=
  (WithLp.toLp 2 (fun index : Fin 3 => raw (index.val + 1)),
    (Encodable.decode (Nat.floor (raw 0))).getD .clock)

theorem input_recovered (input : Input) : inputRead (inputSamples input) = input := by
  apply Prod.ext
  · apply PiLp.ext
    intro index
    simp only [inputRead, inputSamples, dif_pos index.isLt]
  · simp only [inputRead, inputSamples, Nat.floor_natCast, Encodable.encodek, Option.getD_some]

theorem inputSamples_injective : Function.Injective inputSamples :=
  Function.LeftInverse.injective input_recovered

def readReal (law : MotherPointwiseLaws.Law) (channel : Channel) (point : StageNineSpatialPoint) : ℝ :=
  MotherPointwiseLaws.eval law (inputSamples (point, channel)) 0

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRawCurrent
