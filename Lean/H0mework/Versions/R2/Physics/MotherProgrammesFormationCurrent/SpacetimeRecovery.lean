import H0mework.Versions.R2.Physics.MotherProgrammesFormationCurrent.SpacetimeSamples
import H0mework.Versions.R2.Physics.MotherLaws.CurrentConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholeSpacetimeMaterial

open Stage9C.Revision

noncomputable section

def encode (current : SpinPair.Current) : MotherStreamFormation.Carrier :=
  CurrentSampleAction.readInverse (samples current)

theorem read_encode (current : SpinPair.Current) :
    MotherStreamFormation.read (encode current) = samples current :=
  CurrentSampleAction.read_readInverse _

local instance instNonemptyCurrent_scratch : Nonempty SpinPair.Current := ⟨.ingress⟩

/-- The inverse is derived from the fixed physical sampling map's injectivity. -/
def decodeSamples : (ℕ → ℝ) → SpinPair.Current := Function.invFun samples

theorem decodeSamples_samples (current : SpinPair.Current) :
    decodeSamples (samples current) = current :=
  Function.leftInverse_invFun samples_injective current

def decode (material : MotherStreamFormation.Carrier) : SpinPair.Current :=
  decodeSamples (MotherStreamFormation.read material)

theorem decode_encode (current : SpinPair.Current) : decode (encode current) = current := by
  rw [decode, read_encode, decodeSamples_samples]

theorem wholeField_recovered (current : SpinPair.Current) :
    Recognition.wholeField (decode (encode current)) = Recognition.wholeField current := by
  rw [decode_encode]

theorem encode_injective : Function.Injective encode := by
  intro left right same
  exact samples_injective ((read_encode left).symm.trans
    ((congrArg MotherStreamFormation.read same).trans (read_encode right)))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholeSpacetimeMaterial
